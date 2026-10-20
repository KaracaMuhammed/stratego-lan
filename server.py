#!/usr/bin/env python3
"""Stratego home-network server.      Run:  python server.py

No packages to install (Python 3.8+). It prints an address; open it on every
device (PC, phone...) connected to your home Wi-Fi.

HOW THE GAME WORKS (big picture)
  * The SERVER (this file) owns the real game. It knows every piece and checks
    every rule. Players cannot cheat because the browser only sends "I want to
    move from A to B" and the server decides if that is allowed.
  * The BROWSER (web/index.html) asks the server "what is the state?" every
    0.6 s and draws it. It never receives the enemy's hidden pieces.

LEAVING A GAME: nobody can drop out of a running game alone. One player asks, the other must accept
(see room_action). When the game is over, a player can simply go back to the home screen.

THE FILE IS SPLIT IN 4 PARTS - search for the "=====" lines:
  1. RULES     board, pieces, moves, combat      <- edit to change the rules
  2. COMPUTER  the AI opponent                   <- edit to make it smarter
  3. ROOMS     who is playing in which game
  4. HTTP API  the URLs the web page calls
"""

import os
import json, random, secrets, socket, threading
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler
from pathlib import Path
from urllib.parse import urlparse, parse_qs

PORT = 8000                                   # change if 8000 is already used
WEB_DIR = Path(__file__).parent / "web"       # folder with index.html and busts/
AI_DELAY = 0.7                                # seconds the computer "thinks"

# =====================================================================
# 1. RULES
# =====================================================================
SIZE = 10   # the board is SIZE x SIZE squares

# Every kind of pawn.   count = how many each player has
#                       rank  = who wins a fight (higher beats lower)
#                       move  = False for pawns that never move
# Bomb, flag and spy have special fight rules: see battle().
PIECE_TYPES = {
    "flag":       {"count": 1, "rank": 0,  "move": False},
    "bomb":       {"count": 6, "rank": 11, "move": False},
    "spy":        {"count": 1, "rank": 1,  "move": True},
    "scout":      {"count": 8, "rank": 2,  "move": True},
    "miner":      {"count": 5, "rank": 3,  "move": True},
    "sergeant":   {"count": 4, "rank": 4,  "move": True},
    "lieutenant": {"count": 4, "rank": 5,  "move": True},
    "captain":    {"count": 4, "rank": 6,  "move": True},
    "major":      {"count": 3, "rank": 7,  "move": True},
    "colonel":    {"count": 2, "rank": 8,  "move": True},
    "general":    {"count": 1, "rank": 9,  "move": True},
    "marshal":    {"count": 1, "rank": 10, "move": True},
}

# Rows each player starts in (first row, last row). Row 0 is the top of the board.
SETUP_ROWS = {"red": (0, 3), "blue": (6, 9)}

# Blocked squares (the "lakes"), written as (x, y). x = column, y = row.
LAKES = {(2, 4), (3, 4), (2, 5), (3, 5), (6, 4), (7, 4), (6, 5), (7, 5)}


def other(color):
    """The opposite colour."""
    return "red" if color == "blue" else "blue"


def place_army(board, color):
    """Randomly put all 40 pawns of `color` in that player's 4 start rows.
    A pawn is a dict: {"id": "blue-7", "type": "scout", "color": "blue"}.
    The id stays with the pawn for the whole game."""
    types = [t for t, info in PIECE_TYPES.items() for _ in range(info["count"])]
    random.shuffle(types)
    first_row = SETUP_ROWS[color][0]
    for n, t in enumerate(types):
        board[first_row + n // SIZE][n % SIZE] = {"id": f"{color}-{n}", "type": t, "color": color}


def new_state():
    """A fresh game. The whole game is this one dictionary:
      board         SIZE x SIZE grid; each square is None or a pawn
      phase         "setup" (arranging pawns) -> "play" -> "over"
      turn          whose turn it is during "play"
      ready         has each player pressed Ready?
      winner        None, "blue" or "red"
      last_battle   details of the latest fight (the web page animates it)
      battle_seq    counts fights; the page plays an animation when it grows
      move_seq      counts every move (fights included); the page plays the move sound when it grows
      last_move     {from, to, color, fight} of the latest move: the page draws an arrow for it
      dead          pawn types each colour has lost, shown in the side trays
      known         pawn id -> type, ONLY used by the computer's memory"""
    board = [[None] * SIZE for _ in range(SIZE)]
    place_army(board, "blue")
    place_army(board, "red")
    return {"board": board, "phase": "setup", "turn": "blue",
            "ready": {"blue": False, "red": False}, "winner": None,
            "last_battle": None, "battle_seq": 0, "move_seq": 0, "last_move": None,
            "dead": {"blue": [], "red": []}, "known": {}}


def valid_moves(board, x, y):
    """List of [x, y] squares the pawn standing on (x, y) may go to or attack."""
    p = board[y][x]
    if not p or not PIECE_TYPES[p["type"]]["move"]:
        return []                                         # empty square, bomb or flag
    steps = SIZE if p["type"] == "scout" else 1           # scouts may slide far
    moves = []
    for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):     # right, left, down, up
        for s in range(1, steps + 1):
            nx, ny = x + dx * s, y + dy * s
            if not (0 <= nx < SIZE and 0 <= ny < SIZE) or (nx, ny) in LAKES:
                break                                     # edge of board or lake
            target = board[ny][nx]
            if target is None:
                moves.append([nx, ny])                    # free square: keep sliding
                continue
            if target["color"] != p["color"]:
                moves.append([nx, ny])                    # enemy: can attack it...
            break                                         # ...but never go past a pawn
    return moves


def has_any_move(board, color):
    """True if at least one pawn of `color` can move (used for the "stuck" loss)."""
    return any(p and p["color"] == color and valid_moves(board, x, y)
               for y, row in enumerate(board) for x, p in enumerate(row))


def battle(attacker, defender):
    """Who wins a fight? Returns "attacker", "defender" or "both" (both die)."""
    if defender["type"] == "flag":
        return "attacker"                                 # capturing the flag wins
    if defender["type"] == "bomb":
        return "attacker" if attacker["type"] == "miner" else "defender"
    if attacker["type"] == "spy" and defender["type"] == "marshal":
        return "attacker"                                 # spy only wins when it attacks
    a = PIECE_TYPES[attacker["type"]]["rank"]
    d = PIECE_TYPES[defender["type"]]["rank"]
    return "both" if a == d else ("attacker" if a > d else "defender")


def in_zone(color, y):
    """Is row y inside this player's start area?"""
    return SETUP_ROWS[color][0] <= y <= SETUP_ROWS[color][1]


def apply_action(state, player, action):
    """The ONLY place where the game changes. `action` comes from the web page:
         {"type": "SWAP", "from": [x, y], "to": [x, y]}   swap two of my pawns (setup)
         {"type": "RESHUFFLE"}                            re-randomise my pawns (setup)
         {"type": "READY"}                                I am done arranging
         {"type": "MOVE", "from": [x, y], "to": [x, y]}   move / attack
    Returns None when OK, or a short error message (the page just ignores it)."""
    kind = action.get("type")
    board = state["board"]
    try:
        if kind == "SWAP":
            (fx, fy), (tx, ty) = action["from"], action["to"]
            if state["phase"] != "setup" or state["ready"][player]:
                return "Cannot rearrange now"
            if not (in_zone(player, fy) and in_zone(player, ty)):
                return "Outside your zone"
            board[fy][fx], board[ty][tx] = board[ty][tx], board[fy][fx]

        elif kind == "RESHUFFLE":
            if state["phase"] != "setup" or state["ready"][player]:
                return "Cannot shuffle now"
            place_army(board, player)

        elif kind == "READY":
            if state["phase"] != "setup":
                return "Not in setup"
            state["ready"][player] = True
            if all(state["ready"].values()):              # both ready -> blue starts
                state["phase"], state["turn"] = "play", "blue"

        elif kind == "MOVE":
            (fx, fy), (tx, ty) = action["from"], action["to"]
            if state["phase"] != "play" or state["turn"] != player:
                return "Not your turn"
            piece = board[fy][fx]
            if not piece or piece["color"] != player or [tx, ty] not in valid_moves(board, fx, fy):
                return "Illegal move"
            defender = board[ty][tx]
            state["move_seq"] += 1
            state["last_move"] = {"from": [fx, fy], "to": [tx, ty], "color": player, "fight": defender is not None}
            board[fy][fx] = None
            if defender is None:                          # plain move
                board[ty][tx] = piece
            else:                                         # FIGHT
                result = battle(piece, defender)
                state["battle_seq"] += 1
                # Pawns are NOT permanently revealed: the web page shows them for
                # the animation, then they "close" again. The computer remembers.
                state["known"][piece["id"]] = piece["type"]
                state["known"][defender["id"]] = defender["type"]
                if result in ("attacker", "both"):
                    state["dead"][defender["color"]].append(defender["type"])
                if result in ("defender", "both"):
                    state["dead"][piece["color"]].append(piece["type"])
                board[ty][tx] = piece if result == "attacker" else defender if result == "defender" else None
                state["last_battle"] = {"seq": state["battle_seq"], "from": [fx, fy], "to": [tx, ty],
                                        "attacker": dict(piece), "defender": dict(defender), "result": result}
                if defender["type"] == "flag":
                    state["winner"] = player
            if not state["winner"] and not has_any_move(board, other(player)):
                state["winner"] = player                  # the opponent cannot move
            state["phase"] = "over" if state["winner"] else "play"
            state["turn"] = other(player)
        else:
            return "Unknown action"
    except (KeyError, IndexError, TypeError, ValueError):
        return "Bad action"                               # malformed request
    return None


def view_for(room, player):
    """What `player` is allowed to know. This is what is sent to the web page.
    Enemy pawns are sent WITHOUT their type ("hidden": True), except when the
    game is over. `moves` lists where each of your pawns can go, so the page
    does not need its own copy of the movement rules."""
    s = room["state"]
    show_all = s["phase"] == "over"
    board = [[p if (p is None or show_all or p["color"] == player)
              else {"id": p["id"], "color": p["color"], "hidden": True}
              for p in row] for row in s["board"]]
    moves = {}
    if s["phase"] == "play" and s["turn"] == player:
        for y, row in enumerate(s["board"]):
            for x, p in enumerate(row):
                if p and p["color"] == player and valid_moves(s["board"], x, y):
                    moves[f"{x},{y}"] = valid_moves(s["board"], x, y)
    return {"board": board, "phase": s["phase"], "turn": s["turn"], "ready": s["ready"],
            "winner": s["winner"], "last_battle": s["last_battle"], "battle_seq": s["battle_seq"], "move_seq": s["move_seq"],
            "dead": s["dead"], "moves": moves, "you": player,
            "opponent_joined": room["tokens"][other(player)] is not None, "vs_ai": room["ai"],
            "last_move": s["last_move"], "leave": room["leave"], "closed": room["closed"],
            # a notice (toast message) is only shown to the player it is meant for
            "notice": {"seq": room["notice"]["seq"], "text": room["notice"]["text"] if room["notice"]["to"] == player else ""}}


# =====================================================================
# 2. COMPUTER OPPONENT (always plays red)
# =====================================================================
def ai_choose(state):
    """Scores every legal red move and returns the best one. Edit the numbers
    below to change its personality."""
    best, best_score = None, -999
    for y, row in enumerate(state["board"]):
        for x, p in enumerate(row):
            if not p or p["color"] != "red":
                continue
            rank = PIECE_TYPES[p["type"]]["rank"]
            for tx, ty in valid_moves(state["board"], x, y):
                target = state["board"][ty][tx]
                score = random.random()                   # a little randomness
                score += (ty - y) * 0.6                   # red advances downward
                if target:
                    known = state["known"].get(target["id"])   # types the AI has seen
                    if known:                             # it remembers this pawn
                        wins = known == "flag" or rank > PIECE_TYPES[known]["rank"]
                        score += 5 if wins else -3
                    elif rank >= 4 and p["type"] != "spy":
                        score += 2                        # gamble with strong pawns
                    else:
                        score -= 1                        # don't gamble with weak ones
                if score > best_score:
                    best, best_score = {"type": "MOVE", "from": [x, y], "to": [tx, ty]}, score
    return best


def ai_turn(room):
    """Runs in a timer thread: the computer plays one move if it is its turn."""
    with LOCK:
        s = room["state"]
        if room["ai"] and s["phase"] == "play" and s["turn"] == "red":
            move = ai_choose(s)
            if move:
                apply_action(s, "red", move)


def schedule_ai(room):
    """After any human action: if it is now the computer's turn, play soon."""
    s = room["state"]
    if room["ai"] and s["phase"] == "play" and s["turn"] == "red":
        threading.Timer(AI_DELAY, ai_turn, [room]).start()


# =====================================================================
# 3. ROOMS
# =====================================================================
LOCK = threading.Lock()   # the server handles several requests at once; this keeps
                          # them from changing the game at the same moment
ROOMS = {}                # room name -> {"state", "tokens": {"blue","red"}, "ai"}
                          # a token is a secret code that proves who you are


def clean_room(raw):
    """Room IDs are 6 letters/digits, always upper case (the page makes them; the server is tolerant)."""
    return str(raw or "").strip().upper()[:12]


def new_room(vs_ai):
    """tokens: secret code of each seat (None = free seat)
    leave:  {"by": colour} while someone has asked to leave and waits for the answer
    notice: a short message for one player (the page shows it as a toast)
    closed: True when both players agreed to leave"""
    room = {"state": new_state(), "tokens": {"blue": None, "red": None}, "ai": vs_ai,
            "leave": None, "notice": {"seq": 0, "text": "", "to": None}, "closed": False, "seen_closed": set()}
    if vs_ai:
        room["tokens"]["red"] = "computer"
        room["state"]["ready"]["red"] = True               # the computer is always ready
    return room


def join_room(name, vs_ai):
    """Takes the first free seat (blue, then red). Returns (token, color)
    or raises ValueError(message) when the room cannot be joined."""
    room = ROOMS.get(name)
    if room is None or room["closed"]:                     # new room (or an old one both players left)
        room = ROOMS[name] = new_room(vs_ai)
    elif room["ai"]:
        raise ValueError("That room is a game against the computer")
    color = next((c for c in ("blue", "red") if room["tokens"][c] is None), None)
    if color is None:
        raise ValueError("Room is full")
    token = secrets.token_hex(8)
    room["tokens"][color] = token
    return token, color


def find_player(room, token):
    """Which colour does this token belong to? None if unknown."""
    for color in ("blue", "red"):
        if room and token and room["tokens"][color] == token:
            return color
    return None


def notify(room, text, to):
    """Sends a short message to one player (shown once as a toast by the page)."""
    room["notice"] = {"seq": room["notice"]["seq"] + 1, "text": text, "to": to}


def room_action(name, room, player, action):
    """Actions about the ROOM, not about the board. Returns True if `action` was one of them.
         LEAVE_REQUEST  I want to leave. The opponent has to accept (nobody to ask = I just leave)
         LEAVE_CANCEL   I changed my mind
         LEAVE_ACCEPT   the opponent asked to leave and I agree -> the room is closed for both
         LEAVE_DECLINE  I refuse -> the opponent gets a message
         LEAVE_NOW      go back to the home screen (only when the game is over, or alone / vs computer)"""
    kind = action.get("type")
    opponent = other(player)
    alone = room["ai"] or room["tokens"][opponent] is None
    leave = room["leave"]
    if kind == "LEAVE_REQUEST":
        if alone:
            ROOMS.pop(name, None)
        elif leave is None:
            room["leave"] = {"by": player}
        elif leave["by"] == opponent:                      # both asked at the same time = both agree
            room["closed"], room["leave"] = True, None
    elif kind == "LEAVE_CANCEL":
        if leave and leave["by"] == player:
            room["leave"] = None
    elif kind == "LEAVE_ACCEPT":
        if leave and leave["by"] == opponent:
            room["closed"], room["leave"] = True, None
    elif kind == "LEAVE_DECLINE":
        if leave and leave["by"] == opponent:
            room["leave"] = None
            notify(room, "Your opponent declined to leave the game.", opponent)
    elif kind == "LEAVE_NOW":
        if room["state"]["phase"] == "over" or alone:
            room["tokens"][player] = None
            room["leave"] = None
            if alone or all(t is None for t in room["tokens"].values()):
                ROOMS.pop(name, None)
            else:
                notify(room, "Your opponent went back to the home screen.", opponent)
    else:
        return False
    return True


def reset_game(room):
    """New game in the same room with the same players."""
    room["leave"] = None
    room["state"] = new_state()
    if room["ai"]:
        room["state"]["ready"]["red"] = True


# =====================================================================
# 4. HTTP API  (the web page talks to these URLs)
#    GET  /api/state?room=..&token=..   current view for this player
#    POST /api/join    {room, ai}       enter a room -> {token, color}
#    POST /api/action  {room, token, action}   play -> new view
#    anything else = a file from the web/ folder (index.html, busts/*.png)
# =====================================================================
class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(WEB_DIR), **kwargs)

    def log_message(self, *args):
        pass                                               # no console spam

    def send_json(self, data, status=200):
        body = json.dumps(data).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def deliver(self, name, room, player):
        """The answer for a player. When a room is closed, forget it once both players have seen that."""
        view = view_for(room, player)
        if room["closed"]:
            room["seen_closed"].add(player)
            if len(room["seen_closed"]) >= 2:
                ROOMS.pop(name, None)
        return view

    def do_GET(self):
        url = urlparse(self.path)
        if url.path != "/api/state":
            return super().do_GET()                        # serve a normal file
        q = {k: v[0] for k, v in parse_qs(url.query).items()}
        name = clean_room(q.get("room"))
        with LOCK:
            room = ROOMS.get(name)
            player = find_player(room, q.get("token"))
            if not player:
                return self.send_json({"error": "Unknown game - rejoin"}, 404)
            self.send_json(self.deliver(name, room, player))

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers.get("Content-Length", 0))) or b"{}")
        path = urlparse(self.path).path
        name = clean_room(body.get("room"))
        with LOCK:
            if path == "/api/join":
                if not name:
                    return self.send_json({"error": "Room ID is missing"}, 400)
                try:
                    token, color = join_room(name, bool(body.get("ai")))
                except ValueError as e:
                    return self.send_json({"error": str(e)}, 400)
                return self.send_json({"token": token, "color": color})
            if path == "/api/action":
                room = ROOMS.get(name)
                player = find_player(room, body.get("token"))
                if not player:
                    return self.send_json({"error": "Unknown game - rejoin"}, 404)
                action = body.get("action", {})
                if not room_action(name, room, player, action):       # not about leaving: a game action
                    if action.get("type") == "NEW_GAME":
                        if room["state"]["phase"] == "over":          # "Play again" only after a finished game
                            reset_game(room)
                    else:
                        apply_action(room["state"], player, action)
                    schedule_ai(room)
                if name not in ROOMS:                                  # the player left and the room is gone
                    return self.send_json({"left": True})
                return self.send_json(self.deliver(name, room, player))
        self.send_json({"error": "Not found"}, 404)


def lan_ip():
    """This PC's address on the home network (for the other devices)."""
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))                   # nothing is actually sent
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"



if __name__ == "__main__":
    port = int(os.environ.get("PORT", PORT))

    print("Stratego server running.")
    print(f"HTTP server listening on port {port}")

    ThreadingHTTPServer(
        ("0.0.0.0", port),
        Handler
    ).serve_forever()

