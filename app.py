import sys
import os
import shutil
import time
import subprocess
from datetime import datetime, timedelta
import xml.etree.ElementTree as ET
import xml.dom.minidom as minidom
import threading
from threading import Thread
import logging
logger = logging.getLogger("MacReplayV2")
logger.setLevel(logging.INFO)
logFormat = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s")

# Log to Windows "MacReplayV2" folder under APPDATA
if os.name == "nt":
    appdata_path = os.getenv("APPDATA", os.path.expanduser("~\\AppData\\Roaming"))
    log_dir = os.path.join(appdata_path, "MacReplayV2")
    os.makedirs(log_dir, exist_ok=True)
    logFilePath = os.path.join(log_dir, "app.log")
else:
    # Linux: log to current directory under ./MacReplayV2
    log_dir = os.path.join(os.getcwd(), "MacReplayV2")
    os.makedirs(log_dir, exist_ok=True)
    logFilePath = os.path.join(log_dir, "app.log")

fileHandler = logging.FileHandler(logFilePath)
fileHandler.setFormatter(logFormat)
logger.addHandler(fileHandler)

# Also log to stderr
consoleHandler = logging.StreamHandler(sys.stderr)
consoleHandler.setFormatter(logFormat)
logger.addHandler(consoleHandler)

logger.info("Starting MacReplayV2")


try:
    import requests
    from requests.adapters import HTTPAdapter
    from flask import Flask, jsonify, render_template, request, redirect, Response, flash, session
    from flask_limiter import Limiter
    from flask_limiter.util import get_remote_address
    from waitress import serve
except ImportError as e:
    logger.error(f"Failed to import required modules: {e}")
    sys.exit(1)


app = Flask(__name__)
# CORS workaround: allow /xmltv.xml and /lineup* in some environments
try:
    from flask_cors import CORS
    CORS(app, resources={
        r"/xmltv.xml": {"origins": "*"},
        r"/lineup*": {"origins": "*"}
    })
except ImportError:
    logger.warning("flask_cors not installed, CORS headers will not be added.")

limiter = Limiter(
    get_remote_address,
    app=app,
    default_limits=["200 per day", "50 per hour"]
)

try:
    from stb import stb
except Exception as e:
    logger.error(f"Failed to import stb module: {e}")
    sys.exit(1)

import json
import socket
import re
import random

app.secret_key = "1234"

configFile = "MacReplayV2.json"
legacyConfigFile = "MacReplay.json"
xmltv_url = ""  # Placeholder for dynamic XMLTV URL

HDHR_DEVICE_ID = "FFFFFFFF"  # 8-digit hex; not used as much for real devices

occupied = {}
lastConnection = {}
lastEpgRefresh = 0
currentlyRefreshingEpg = False
epg_cache = {}
cached_xmltv = None
last_updated = 0


d_ffmpegcmd = [
    "-re",                      # Flag for real-time streaming
    "-http_proxy", "<proxy>",   # Proxy setting
    "-timeout", "<timeout>",    # Timeout setting
    "-i", "<url>",              # Input URL
    "-map", "0",                # Map all streams
    "-codec", "copy",           # Copy codec (no re-encoding)
    "-f", "mpegts",             # Output format
    "-flush_packets", "0",      # Disable flushing packets (optimized for faster output)
    "-fflags", "+nobuffer",     # No buffering for low latency
    "-flags", "low_delay", 
    "-strict", "experimental",
    "pipe:1"                    # Output to stdout
]


cached_playlist = None
last_playlist_host = None

# default settings
defaultSettings = {
    "HDHomeRun enabled": "true",
    "HDHomeRun-like mode": "true",
    "playlist on startup": "true",
    "stream method": "ffmpeg",
    "ffmpeg path": "ffmpeg",
    "ffprobe path": "ffprobe",
    "ffmpeg command": "ffmpeg.exe -loglevel panic -re -http_proxy <proxy> -timeout <timeout> -i <url> -map 0 -codec copy -f mpegts -flush_packets 0 -fflags +nobuffer -flags low_delay -strict experimental pipe:1",
    "ffmpeg drop detection": "true",
    "ffprobe timeout": "10000000",
    "stream timeout": "10000000",
    "streams per mac": "1",
    "use epg": "true",
    "use channel numbers": "true",
    "use channel genres": "true",
    "EPG enabled": "true",
    "EPG days": 3,
    "EPG refresh interval": 12,
    "max concurrent streams": 20,
    "sort playlist by channel genre": "false",
    "sort playlist by channel number": "true",
    "sort playlist by channel name": "false",
}

config = {
    "settings": defaultSettings,
    "portals": {},
}

# custom Jinja2 filter for JSON serialization
@app.template_filter('tojsonfilter')
def tojson_filter(obj):
    return json.dumps(obj)

basePath = os.path.abspath(os.getcwd())

if os.getenv("HOST"):
    host = os.getenv("HOST")
else:
    host = "ubuntu.verbergwest.appboxes.co:13681"
logger.info(f"Server started on http://{host}")

try:
    EPG_REFRESH_INTERVAL_HOURS = float(os.getenv("EPG_REFRESH_INTERVAL_HOURS", "12"))
except ValueError:
    EPG_REFRESH_INTERVAL_HOURS = 12.0

def loadConfig():
    global config
    if os.path.exists(configFile):
        try:
            with open(configFile, "r") as f:
                config = json.load(f)
            logger.info(f"Loaded configuration from {configFile}")
        except Exception as e:
            logger.error(f"Failed to load configuration: {e}")
            config = {"settings": defaultSettings.copy(), "portals": {}}
    else:
        # Try migrating from legacy MacReplay.json
        if os.path.exists(legacyConfigFile):
            try:
                shutil.copy2(legacyConfigFile, configFile)
                with open(configFile, "r") as f:
                    config = json.load(f)
                logger.info("Legacy MacReplay config detected – migrated to MacReplayV2.json")
            except Exception as e:
                logger.error(f"Failed to migrate legacy configuration: {e}")
                config = {"settings": defaultSettings.copy(), "portals": {}}
        else:
            config = {"settings": defaultSettings.copy(), "portals": {}}
            saveConfig()


def saveConfig():
    try:
        with open(configFile, "w") as f:
            json.dump(config, f, indent=4)
        logger.info(f"Configuration saved to {configFile}")
    except Exception as e:
        logger.error(f"Failed to save configuration: {e}")


def getSettings():
    return config["settings"]


def getPortals():
    return config["portals"]


def getSettingValue(key):
    return getSettings().get(key, defaultSettings.get(key))


def authorise(f):
    def wrap(*args, **kwargs):
        if "logged_in" in session and session["logged_in"]:
            return f(*args, **kwargs)
        else:
            return redirect("/login", code=302)
    wrap.__name__ = f.__name__
    return wrap


def isStreamAllowed():
    max_streams = int(getSettings().get("max concurrent streams", 20))
    if max_streams <= 0:
        return True
    current_streams = sum(len(occupied.get(portal, [])) for portal in occupied)
    return current_streams < max_streams


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        password = request.form.get("password")
        if password == getSettings().get("admin password", "admin"):
            session["logged_in"] = True
            logger.info("User logged in successfully.")
            return redirect("/", code=302)
        else:
            flash("Incorrect password", "danger")
            logger.warning("Failed login attempt.")
            return render_template("login.html")
    return render_template("login.html")


@app.route("/logout", methods=["GET"])
def logout():
    session.pop("logged_in", None)
    logger.info("User logged out.")
    return redirect("/login", code=302)


@app.route("/", methods=["GET"])
@authorise
def dashboard():
    portals = getPortals()
    totalChannels = 0
    for portal in portals:
        if portals[portal]["enabled"] == "true":
            totalChannels = totalChannels + len(
                portals[portal].get("enabled channels", [])
            )
    return render_template(
        "dashboard.html",
        settings=getSettings(),
        portals=portals,
        totalChannels=totalChannels,
    )


@app.route("/editor", methods=["GET"])
@authorise
def editor():
    return render_template("editor.html")
    


@app.route("/editor_data", methods=["GET"])
@authorise
def editor_data():
    portals = getPortals()
    channels = []

    for portal in portals:
        logger.info(f"getting Data from {portal}")
        if portals[portal]["enabled"] == "true":
            portalName = portals[portal]["name"]
            url = portals[portal]["url"]
            macs = list(portals[portal]["macs"].keys())
            proxy = portals[portal]["proxy"]
            enabledChannels = portals[portal].get("enabled channels", [])
            customChannelNames = portals[portal].get("custom channel names", {})
            customGenres = portals[portal].get("custom genres", {})
            customChannelNumbers = portals[portal].get("custom channel numbers", {})
            customEpgIds = portals[portal].get("custom epg ids", {})
            fallbackChannels = portals[portal].get("fallback channels", {})

            for mac in macs:
                logger.info(f"Using mac: {mac}")
                token = None
                allChannels = None
                genres = None
                try:
                    token = stb.getToken(url, mac, proxy)
                    stb.getProfile(url, mac, token, proxy)
                    allChannels = stb.getAllChannels(url, mac, token, proxy)
                    genres = stb.getGenreNames(url, mac, token, proxy)
                    break
                except Exception as e:
                    logger.error(f"Failed to retrieve data for Portal({portal}) MAC {mac}: {e}")
                    allChannels = None
                    genres = None

            if allChannels and genres:
                for channel in allChannels:
                    channelId = str(channel["id"])
                    channelName = str(channel["name"])
                    channelNumber = str(channel["number"])
                    genre = str(genres.get(str(channel["tv_genre_id"])))
                    if channelId in enabledChannels:
                        enabled = True
                    else:
                        enabled = False
                    customChannelNumber = customChannelNumbers.get(channelId)
                    if customChannelNumber == None:
                        customChannelNumber = ""
                    customChannelName = customChannelNames.get(channelId)
                    if customChannelName == None:
                        customChannelName = ""
                    customGenre = customGenres.get(channelId)
                    if customGenre == None:
                        customGenre = ""
                    customEpgId = customEpgIds.get(channelId)
                    if customEpgId == None:
                        customEpgId = ""
                    fallbackChannel = fallbackChannels.get(channelId)
                    if fallbackChannel == None:
                        fallbackChannel = ""
                    channels.append(
                        {
                            "portal": portal,
                            "portalName": portalName,
                            "enabled": enabled,
                            "channelNumber": channelNumber,
                            "customChannelNumber": customChannelNumber,
                            "channelName": channelName,
                            "customChannelName": customChannelName,
                            "genre": genre,
                            "customGenre": customGenre,
                            "customEpgId": customEpgId,
                            "fallbackChannel": fallbackChannel,
                        }
                    )
            else:
                logger.error("Error making editor data for {}, skipping".format(portal))

    return jsonify({"channels": channels})


@app.route("/editor", methods=["POST"])
@authorise
def editor_post():
    channels = request.json.get("channels", [])

    portals = getPortals()

    for channel in channels:
        portal = channel.get("portal")
        channelId = channel.get("channelId")
        enabled = channel.get("enabled")
        customChannelNumber = channel.get("customChannelNumber")
        customChannelName = channel.get("customChannelName")
        customGenre = channel.get("customGenre")
        customEpgId = channel.get("customEpgId")
        fallbackChannel = channel.get("fallbackChannel")

        if portal not in portals:
            continue

        enabledChannels = portals[portal].get("enabled channels", [])
        if enabled:
            if channelId not in enabledChannels:
                enabledChannels.append(channelId)
        else:
            if channelId in enabledChannels:
                enabledChannels.remove(channelId)
        portals[portal]["enabled channels"] = enabledChannels

        customChannelNumbers = portals[portal].get("custom channel numbers", {})
        if customChannelNumber:
            customChannelNumbers[channelId] = customChannelNumber
        else:
            customChannelNumbers.pop(channelId, None)
        portals[portal]["custom channel numbers"] = customChannelNumbers

        customChannelNames = portals[portal].get("custom channel names", {})
        if customChannelName:
            customChannelNames[channelId] = customChannelName
        else:
            customChannelNames.pop(channelId, None)
        portals[portal]["custom channel names"] = customChannelNames

        customGenres = portals[portal].get("custom genres", {})
        if customGenre:
            customGenres[channelId] = customGenre
        else:
            customGenres.pop(channelId, None)
        portals[portal]["custom genres"] = customGenres

        customEpgIds = portals[portal].get("custom epg ids", {})
        if customEpgId:
            customEpgIds[channelId] = customEpgId
        else:
            customEpgIds.pop(channelId, None)
        portals[portal]["custom epg ids"] = customEpgIds

        fallbackChannels = portals[portal].get("fallback channels", {})
        if fallbackChannel:
            fallbackChannels[channelId] = fallbackChannel
        else:
            fallbackChannels.pop(channelId, None)
        portals[portal]["fallback channels"] = fallbackChannels

    saveConfig()
    return jsonify({"success": True})


@app.route("/portals", methods=["GET"])
@authorise
def portals():
    return render_template("portals.html", settings=getSettings(), portals=getPortals())


@app.route("/settings", methods=["GET"])
@authorise
def settings():
    return render_template("settings.html", settings=getSettings(), portals=getPortals())


@app.route("/setCurrentPortal", methods=["GET"])
@authorise
def setCurrentPortal():
    portal = request.args.get("portal", "")
    portals = getPortals()

    if portal in portals:
        settings = getSettings()
        settings["currentPortal"] = portal
        saveConfig()
        flash("Current portal set to {}".format(portal), "success")
    else:
        flash("Portal does not exist", "danger")

    return redirect("/", code=302)


@app.route("/settings", methods=["POST"])
@authorise
def settings_post():
    settings = getSettings()

    hdhrEnabled = request.form.get("hdhr enabled", "false")
    settings["HDHomeRun enabled"] = hdhrEnabled

    if hdhrEnabled == "true":
        enable_hdhomerun()
    else:
        disable_hdhomerun()

    settings["HDHomeRun-like mode"] = request.form.get("HDHomeRun-like mode", "true")
    settings["admin password"] = request.form.get("admin password", "admin")
    settings["streams per mac"] = request.form.get("streams per mac", "1")
    settings["ffmpeg path"] = request.form.get("ffmpeg path", "ffmpeg")
    settings["ffprobe path"] = request.form.get("ffprobe path", "ffprobe")
    settings["ffmpeg command"] = request.form.get(
        "ffmpeg command", defaultSettings["ffmpeg command"]
    )
    settings["ffmpeg drop detection"] = request.form.get(
        "ffmpeg drop detection", "true"
    )
    settings["ffprobe timeout"] = request.form.get("ffprobe timeout", "10000000")
    settings["stream timeout"] = request.form.get("stream timeout", "10000000")
    settings["use epg"] = request.form.get("use epg", "true")
    settings["use channel numbers"] = request.form.get(
        "use channel numbers", "true"
    )
    settings["use channel genres"] = request.form.get("use channel genres", "true")

    settings["EPG enabled"] = request.form.get("EPG enabled", "true")
    settings["EPG days"] = int(request.form.get("EPG days", 3))
    settings["EPG refresh interval"] = int(request.form.get("EPG refresh interval", 12))
    settings["max concurrent streams"] = int(
        request.form.get("max concurrent streams", 20)
    )
    settings["sort playlist by channel name"] = request.form.get(
        "sort playlist by channel name", "true"
    )
    settings["sort playlist by channel number"] = request.form.get(
        "sort playlist by channel number", "true"
    )
    settings["sort playlist by channel genre"] = request.form.get(
        "sort playlist by channel genre", "false"
    )

    saveConfig()
    flash("Settings saved", "success")
    return redirect("/settings", code=302)


@app.route("/addPortal", methods=["POST"])
@authorise
def addPortal():
    portals = getPortals()

    name = request.form.get("name", "").strip()
    url = request.form.get("url", "").strip()
    mac = request.form.get("mac", "").strip()
    proxy = request.form.get("proxy", "").strip()

    if not name or not url or not mac:
        flash("All fields are required (Name, URL, MAC)", "danger")
        return redirect("/portals", code=302)

    portalId = str(len(portals) + 1)

    portals[portalId] = {
        "name": name,
        "url": url,
        "proxy": proxy,
        "macs": {mac: {"enabled": True}},
        "enabled": "true",
        "enabled channels": [],
        "custom channel names": {},
        "custom channel numbers": {},
        "custom genres": {},
        "custom epg ids": {},
        "fallback channels": {},
    }

    saveConfig()
    flash("Portal ({}) added successfully".format(name), "success")
    return redirect("/portals", code=302)


@app.route("/addMac", methods=["POST"])
@authorise
def addMac():
    portalId = request.form.get("portalid")
    mac = request.form.get("mac", "").strip()

    if not mac or portalId not in getPortals():
        flash("Invalid portal or MAC", "danger")
        return redirect("/portals", code=302)

    try:
        portals = getPortals()
        portals[portalId]["macs"][mac] = {"enabled": True}
        saveConfig()
        flash("MAC ({}) added to Portal ({})".format(mac, portalId), "success")
    except Exception as e:
        logger.error(f"Failed to add MAC: {e}")
        flash("Failed to add MAC", "danger")

    return redirect("/portals", code=302)


@app.route("/delPortal", methods=["POST"])
@authorise
def delPortal():
    portalId = request.form.get("portal")
    portals = getPortals()

    if portalId in portals:
        name = portals[portalId]["name"]
        del portals[portalId]
        saveConfig()
        logger.info("Portal ({}) removed!".format(name))
        flash("Portal ({}) removed!".format(name), "success")
    else:
        flash("Portal does not exist", "danger")

    return redirect("/portals", code=302)


@app.route("/editor", methods=["GET"])
@authorise
def editor_page():
    return render_template("editor.html")


@app.route("/editor", methods=["POST"])
@authorise
def editor_update():
    # This is handled by editor_post above
    return editor_post()


@app.route("/playlist.m3u", methods=["GET"])
@authorise
def playlist():
    global cached_playlist, last_playlist_host
    
    logger.info("Playlist Requested")
    
    # Detect the current host dynamically
    current_host = host
    
    # Regenerate the playlist if it is empty or the host has changed
    if cached_playlist is None or len(cached_playlist) == 0 or last_playlist_host != current_host:
        logger.info(f"Regenerating playlist due to host change: {last_playlist_host} -> {current_host}")
        last_playlist_host = current_host
        generate_playlist()

    return Response(cached_playlist, mimetype="text/plain")
@app.route("/playlist_<portalId>.m3u", methods=["GET"])
@authorise
def playlist_portal(portalId):
    """
    Generate a playlist.m3u containing only channels from a specific portal.

    This is similar to the global /playlist.m3u endpoint, but filtered so that
    only channels belonging to the given portalId are included.
    """
    logger.info(f"Playlist Requested for Portal {portalId}")

    playlist_host = host  # Use the same host that the global playlist uses
    portals = getPortals()

    # Validate portal
    if portalId not in portals:
        logger.warning(f"Requested playlist for unknown portalId: {portalId}")
        return Response("#EXTM3U\n", mimetype="text/plain")

    portal_cfg = portals[portalId]
    if portal_cfg.get("enabled") != "true":
        logger.info(f"Requested playlist for disabled portalId: {portalId}")
        return Response("#EXTM3U\n", mimetype="text/plain")

    enabledChannels = portal_cfg.get("enabled channels", [])
    if not enabledChannels:
        logger.info(f"No enabled channels for portalId: {portalId}")
        return Response("#EXTM3U\n", mimetype="text/plain")

    url = portal_cfg.get("url")
    proxy = portal_cfg.get("proxy")
    macs = list(portal_cfg.get("macs", {}).keys())

    customChannelNames = portal_cfg.get("custom channel names", {})
    customGenres = portal_cfg.get("custom genres", {})
    customChannelNumbers = portal_cfg.get("custom channel numbers", {})
    customEpgIds = portal_cfg.get("custom epg ids", {})

    allChannels = None
    genres = None

    # Try each MAC until one works
    for mac in macs:
        try:
            logger.info(f"Initialising portal {portalId} for playlist with MAC {mac}")
            token = stb.getToken(url, mac, proxy)
            stb.getProfile(url, mac, token, proxy)
            allChannels = stb.getAllChannels(url, mac, token, proxy)
            genres = stb.getGenreNames(url, mac, token, proxy)
            break
        except Exception as e:
            logger.warning(f"Failed to init portal {portalId} with MAC {mac}: {e}")
            allChannels = None
            genres = None

    channels = []
    if allChannels and genres:
        for channel in allChannels:
            channelId = str(channel.get("id"))
            if channelId not in enabledChannels:
                continue

            # Base data from portal
            channelName = str(channel.get("name"))
            channelNumber = str(channel.get("number"))
            genre = str(genres.get(str(channel.get("tv_genre_id"))))

            # Apply custom overrides
            customName = customChannelNames.get(channelId)
            if customName:
                channelName = customName

            customGenre = customGenres.get(channelId)
            if customGenre:
                genre = customGenre

            customNumber = customChannelNumbers.get(channelId)
            if customNumber is not None and customNumber != "":
                channelNumber = customNumber

            epgId = customEpgIds.get(channelId)
            if epgId is None or epgId == "":
                epgId = channelName

            # Build EXTINF line
            line = "#EXTINF:-1" + ' tvg-id="' + epgId + '"'
            if getSettings().get("use channel numbers", "true") == "true":
                line += f' tvg-chno="{channelNumber}"'
            if getSettings().get("use channel genres", "true") == "true":
                line += f'" group-title="{genre}'
            line += f'",{channelName}\nhttp://{playlist_host}/play/{portalId}/{channelId}'

            channels.append(line)

    # Sorting the playlist based on settings (same as global playlist)
    if getSettings().get("sort playlist by channel name", "true") == "true":
        channels.sort(key=lambda k: k.split(",")[1].split("\n")[0])
    if getSettings().get("use channel numbers", "true") == "true":
        if getSettings().get("sort playlist by channel number", "false") == "true":
            channels.sort(key=lambda k: k.split('tvg-chno="')[1].split('"')[0])
    if getSettings().get("use channel genres", "true") == "true":
        if getSettings().get("sort playlist by channel genre", "false") == "true":
            channels.sort(key=lambda k: k.split('group-title="')[1].split('"')[0])

    playlist = "#EXTM3U \n" + "\n".join(channels)
    return Response(playlist, mimetype="text/plain")


@app.route("/m3u/<portalId>", methods=["GET"])
@authorise
def m3u_portal(portalId):
    """Alias endpoint so /m3u/<portalId> also returns a per-portal playlist."""
    return playlist_portal(portalId)

# Function to manually trigger playlist update
@app.route("/update_playlistm3u", methods=["POST"])
def update_playlistm3u():
    generate_playlist()
    return Response("Playlist updated successfully", status=200)

def generate_playlist():
    global cached_playlist
    logger.info("Generating playlist.m3u...")

    # Detect the host dynamically from the request
    playlist_host = host
    
    channels = []
    portals = getPortals()

    for portal in portals:
        if portals[portal]["enabled"] == "true":
            enabledChannels = portals[portal].get("enabled channels", [])
            if len(enabledChannels) != 0:
                name = portals[portal]["name"]
                url = portals[portal]["url"]
                proxy = portals[portal]["proxy"]
                macs = list(portals[portal]["macs"].keys())

                token = None
                allChannels = None
                genres = None
                for mac in macs:
                    try:
                        token = stb.getToken(url, mac, proxy)
                        stb.getProfile(url, mac, token, proxy)
                        allChannels = stb.getAllChannels(url, mac, token, proxy)
                        genres = stb.getGenreNames(url, mac, token, proxy)
                        break
                    except Exception as e:
                        logger.error(f"Failed to retrieve data for Portal({name}) MAC {mac}: {e}")
                        allChannels = None
                        genres = None

                if allChannels and genres:
                    customChannelNames = portals[portal].get("custom channel names", {})
                    customGenres = portals[portal].get("custom genres", {})
                    customChannelNumbers = portals[portal].get("custom channel numbers", {})
                    customEpgIds = portals[portal].get("custom epg ids", {})

                    for channel in allChannels:
                        channelId = str(channel.get("id"))
                        if channelId in enabledChannels:
                            channelName = customChannelNames.get(channelId) or str(channel.get("name"))
                            genre = customGenres.get(channelId) or str(genres.get(str(channel.get("tv_genre_id"))))
                            channelNumber = customChannelNumbers.get(channelId)
                            if channelNumber is None:
                                channelNumber = str(channel.get("number"))
                            epgId = customEpgIds.get(channelId)
                            if epgId is None:
                                epgId = channelName
                            channels.append(
                                "#EXTINF:-1"
                                + ' tvg-id="'
                                + epgId
                                + (
                                    '" tvg-chno="' + channelNumber
                                    if getSettings().get("use channel numbers", "true")
                                    == "true"
                                    else ""
                                )
                                + (
                                    '" group-title="' + genre
                                    if getSettings().get("use channel genres", "true")
                                    == "true"
                                    else ""
                                )
                                + '",'
                                + channelName
                                + "\n"
                                + "http://"
                                + playlist_host  # Use the dynamically detected playlist host
                                + "/play/"
                                + portal
                                + "/"
                                + channelId
                            )
                else:
                    logger.error("Error making playlist for {}, skipping".format(name))

    # Sorting the playlist based on settings
    if getSettings().get("sort playlist by channel name", "true") == "true":
        channels.sort(key=lambda k: k.split(",")[1].split("\n")[0])
    if getSettings().get("use channel numbers", "true") == "true":
        if getSettings().get("sort playlist by channel number", "false") == "true":
            channels.sort(key=lambda k: k.split('tvg-chno="')[1].split('"')[0])
    if getSettings().get("use channel genres", "true") == "true":
        if getSettings().get("sort playlist by channel genre", "false") == "true":
            channels.sort(key=lambda k: k.split('group-title="')[1].split('"')[0])

    playlist = "#EXTM3U \n"
    playlist = playlist + "\n".join(channels)

    # Update the cache
    cached_playlist = playlist


# Function to fetch the latest XMLTV data
def fetch_latest_xmltv():
    global cached_xmltv, last_updated

    if not getSettings().get("EPG enabled", "true") == "true":
        logger.info("EPG is disabled; not fetching XMLTV.")
        return None

    url = xmltv_url
    if not url:
        logger.warning("XMLTV URL not set; cannot fetch XMLTV.")
        return None

    try:
        response = requests.get(url, timeout=15)
        response.raise_for_status()
        cached_xmltv = response.text
        last_updated = time.time()
        logger.info("XMLTV data updated successfully.")
    except Exception as e:
        logger.error(f"Failed to fetch XMLTV data: {e}")
        cached_xmltv = None


def epg_refresh_worker():
    global lastEpgRefresh, currentlyRefreshingEpg, xmltv_url

    while True:
        try:
            if getSettings().get("EPG enabled", "true") == "true":
                logger.info("EPG is enabled; refreshing EPG data...")
                portals = getPortals()
                for portal in portals:
                    if portals[portal]["enabled"] == "true":
                        try:
                            url = portals[portal]["url"]
                            mac = list(portals[portal]["macs"].keys())[0]
                            proxy = portals[portal]["proxy"]
                            token = stb.getToken(url, mac, proxy)
                            stb.getProfile(url, mac, token, proxy)
                            stb.getEpg(url, mac, token, getSettings().get("EPG days", 3), proxy)
                            xmltv_url = f"http://{host}/xmltv.xml"
                            fetch_latest_xmltv()
                        except Exception as e:
                            logger.error(f"Error refreshing EPG for portal {portal}: {e}")
                lastEpgRefresh = time.time()
                currentlyRefreshingEpg = False
                logger.info("EPG refreshed.")
            time.sleep(EPG_REFRESH_INTERVAL_HOURS * 3600)
        except Exception as e:
            logger.error(f"EPG refresh worker encountered an error: {e}")
            time.sleep(60)


Thread(target=epg_refresh_worker, daemon=True).start()


@app.route("/xmltv.xml", methods=["GET"])
def xmltv():
    global cached_xmltv

    if not getSettings().get("EPG enabled", "true") == "true":
        return Response("EPG is disabled.", mimetype="text/plain", status=503)

    if cached_xmltv is None:
        fetch_latest_xmltv()

    if cached_xmltv:
        return Response(cached_xmltv, mimetype="application/xml")
    else:
        return Response("Failed to load XMLTV data.", mimetype="text/plain", status=500)


def enable_hdhomerun():
    logger.info("HDHomeRun emulation enabled.")


def disable_hdhomerun():
    logger.info("HDHomeRun emulation disabled.")


@app.route("/discover.json", methods=["GET"])
def discover():
    if getSettings().get("HDHomeRun enabled", "true") != "true":
        return Response("HDHomeRun emulation is disabled", status=404)

    data = {
        "FriendlyName": "MacReplayV2",
        "ModelNumber": "HDHR4-2US",
        "FirmwareName": "hdhomerun4_atsc",
        "FirmwareVersion": "20211206",
        "DeviceID": HDHR_DEVICE_ID,
        "DeviceAuth": "test1234",
        "BaseURL": f"http://{host}",
        "LineupURL": f"http://{host}/lineup.json",
    }
    return jsonify(data)


@app.route("/lineup_status.json", methods=["GET"])
def lineup_status():
    if getSettings().get("HDHomeRun enabled", "true") != "true":
        return Response("HDHomeRun emulation is disabled", status=404)

    data = {"ScanInProgress": 0, "ScanPossible": 1, "Source": "Cable", "SourceList": ["Cable"]}
    return jsonify(data)


@app.route("/lineup.json", methods=["GET"])
def lineup():
    if getSettings().get("HDHomeRun enabled", "true") != "true":
        return Response("HDHomeRun emulation is disabled", status=404)

    logger.info("Generating Lineup...")
    lineup = []
    portals = getPortals()

    for portalId, portal in portals.items():
        if portal.get("enabled") == "true":
            url = portal["url"]
            macs = list(portal["macs"].keys())
            proxy = portal["proxy"]
            enabledChannels = portal.get("enabled channels", [])
            customChannelNames = portal.get("custom channel names", {})
            customChannelNumbers = portal.get("custom channel numbers", {})

            token = None
            allChannels = None
            for mac in macs:
                try:
                    token = stb.getToken(url, mac, proxy)
                    stb.getProfile(url, mac, token, proxy)
                    allChannels = stb.getAllChannels(url, mac, token, proxy)
                    break
                except Exception as e:
                    logger.error(f"Failed to retrieve lineup for Portal({portalId}) MAC {mac}: {e}")
                    allChannels = None

            if allChannels:
                for channel in allChannels:
                    channelId = str(channel["id"])
                    if channelId in enabledChannels:
                        channelName = customChannelNames.get(channelId) or str(channel.get("name"))
                        channelNumber = customChannelNumbers.get(channelId) or str(channel.get("number"))
                        lineup.append(
                            {
                                "GuideNumber": channelNumber,
                                "GuideName": channelName,
                                "URL": f"http://{host}/play/{portalId}/{channelId}",
                            }
                        )

    return jsonify(lineup)


@app.route("/lineup.post", methods=["POST"])
def lineup_post():
    # HDHomeRun clients may POST here to trigger a scan; we can ignore
    logger.info("Received lineup.post from client")
    return Response("OK", status=200)


def isMacFree(portalId, mac):
    streamsPerMac = int(getSettings().get("streams per mac", 1))
    if streamsPerMac == 0:
        return True

    acquired_by_same_host = 0
    for stream in occupied.get(portalId, []):
        if stream["mac"] == mac:
            acquired_by_same_host += 1

    return acquired_by_same_host < streamsPerMac


def moveMac(portalId, mac):
    portals = getPortals()
    portalMacs = portals[portalId]["macs"]
    if mac in portalMacs:
        portalMacs[mac] = portalMacs.pop(mac)
        saveConfig()


def getChannel(portalId, channelId):
    portal = getPortals().get(portalId)
    if not portal or portal.get("enabled") != "true":
        return None, None, None

    macs = list(portal["macs"].keys())
    if not macs:
        return None, None, None

    proxy = portal.get("proxy")
    url = portal.get("url")

    token = None
    allChannels = None
    genres = None
    freeMac = None
    channelName = None
    streamUrl = None

    for mac in macs:
        if not isMacFree(portalId, mac):
            continue

        try:
            token = stb.getToken(url, mac, proxy)
            stb.getProfile(url, mac, token, proxy)
            allChannels = stb.getAllChannels(url, mac, token, proxy)
            genres = stb.getGenreNames(url, mac, token, proxy)
            freeMac = mac
            break
        except Exception as e:
            logger.error(f"Error initializing MAC {mac} for portal {portalId}: {e}")
            token = None
            allChannels = None
            genres = None

    if not freeMac or not allChannels:
        return None, None, None

    for channel in allChannels:
        if str(channel["id"]) == str(channelId):
            channelName = str(channel["name"])
            streamUrl = (
                url
                + channel["cmd"].split(" ")[0].replace("ffmpeg ", "").replace("/udp/", "udp://@")
            )
            break

    return channelName, streamUrl, freeMac


def testStream(streamUrl, proxy, timeout):
    ffprobe_path = getSettings().get("ffprobe path", "ffprobe")
    ffprobe_cmd = [ffprobe_path, "-loglevel", "error", "-timeout", str(timeout)]
    if proxy:
        ffprobe_cmd.extend(["-http_proxy", proxy])
    ffprobe_cmd.extend(["-i", streamUrl, "-show_streams", "-select_streams", "v:0"])

    try:
        result = subprocess.run(ffprobe_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return result.returncode == 0
    except Exception as e:
        logger.error(f"ffprobe failed: {e}")
        return False


@app.route("/play/<portalId>/<channelId>", methods=["GET"])
def play(portalId, channelId):
    portals = getPortals()
    portal = portals.get(portalId)
    if not portal or portal.get("enabled") != "true":
        return Response("Portal not found or disabled", status=404)

    if not isStreamAllowed():
        return Response("Max concurrent streams reached", status=503)

    channelName, streamUrl, mac = getChannel(portalId, channelId)
    if not streamUrl:
        return Response("Channel not found or no free MAC", status=404)

    proxy = portal.get("proxy")
    ffmpeg_path = getSettings().get("ffmpeg path", "ffmpeg")
    ffmpeg_cmd_template = getSettings().get("ffmpeg command", defaultSettings["ffmpeg command"])
    ffprobe_timeout = int(getSettings().get("ffprobe timeout", 10000000))
    stream_timeout = int(getSettings().get("stream timeout", 10000000))

    if not testStream(streamUrl, proxy, ffprobe_timeout):
        logger.error(f"Stream test failed for {streamUrl}")
        return Response("Stream unavailable", status=503)

    ffmpeg_cmd = ffmpeg_cmd_template.replace("<url>", streamUrl).replace("<proxy>", proxy or "").replace(
        "<timeout>", str(stream_timeout)
    )
    ffmpeg_cmd = ffmpeg_cmd.strip().split()

    def generate():
        global occupied, lastConnection
        proc = None
        try:
            proc = subprocess.Popen(
                ffmpeg_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                bufsize=10**8,
            )
            if portalId not in occupied:
                occupied[portalId] = []
            occupied[portalId].append({"mac": mac, "channelId": channelId})
            lastConnection[portalId] = time.time()

            while True:
                data = proc.stdout.read(1024)
                if not data:
                    break
                yield data

        except Exception as e:
            logger.error(f"Error while streaming: {e}")
        finally:
            if proc:
                proc.kill()
            if portalId in occupied:
                occupied[portalId] = [
                    s for s in occupied[portalId] if not (s["mac"] == mac and s["channelId"] == channelId)
                ]

    return Response(generate(), mimetype="video/mp2t")


if __name__ == "__main__":
    loadConfig()
    if getSettings().get("HDHomeRun enabled", "true") == "true":
        enable_hdhomerun()

    port = 13681
    logger.info(f"Starting server on port {port}")
    serve(app, host="0.0.0.0", port=port)
