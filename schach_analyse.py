#!/usr/bin/env python3
"""Schach-Analyse: Figuren frei platzieren, besten Zug & Drohungen anzeigen.

Start:  python schach_analyse.py      (nur Python 3 + tkinter nötig)

Bedienung
  - Figur aus dem Menü rechts aufs Brett ziehen, beim Loslassen wird sie platziert
  - Alternativ: Figur im Menü anklicken, dann Felder anklicken (nochmal klicken = abwählen)
  - "Brett drehen" (oder Taste F) dreht die Ansicht um 180°
  - Findet das Programm Matt in 1 oder 2 Zügen, erscheint ein blauer Pfeil + Hinweis
  - Gelernte Matt-Muster werden in matt_gedaechtnis.json gespeichert ("Matt-Training" = Selbstspiel)
  - Figuren auf dem Brett ziehen und loslassen = verschieben
  - Rechtsklick auf ein Feld = Figur entfernen
  - Oben: Weiß / Schwarz umschalten, Checkbox für Drohungen
"""
import hashlib
import json
import math
import multiprocessing
import os
import queue
import random
import threading
import time
import tkinter as tk
import tkinter.font as tkfont

# ───────────────────────── Engine ─────────────────────────
PIECE_VAL = {'p': 100, 'n': 320, 'b': 330, 'r': 500, 'q': 900, 'k': 0}
ATT_VAL = dict(PIECE_VAL, k=10000)
MATE, INF = 100000, 10 ** 9
NAME_DE = {'k': 'König', 'q': 'Dame', 'r': 'Turm', 'b': 'Läufer', 'n': 'Springer', 'p': 'Bauer'}

DIAG = [(-1, -1), (-1, 1), (1, -1), (1, 1)]
ORTH = [(-1, 0), (1, 0), (0, -1), (0, 1)]
KN = [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)]
KG = DIAG + ORTH


def _rays(sq, dirs):
    r, c = divmod(sq, 8)
    out = []
    for dr, dc in dirs:
        ray, rr, cc = [], r + dr, c + dc
        while 0 <= rr < 8 and 0 <= cc < 8:
            ray.append(rr * 8 + cc)
            rr, cc = rr + dr, cc + dc
        out.append(ray)
    return out


def _jumps(sq, offs):
    r, c = divmod(sq, 8)
    return [(r + dr) * 8 + c + dc for dr, dc in offs if 0 <= r + dr < 8 and 0 <= c + dc < 8]


DIAG_R = [_rays(s, DIAG) for s in range(64)]
ORTH_R = [_rays(s, ORTH) for s in range(64)]
KN_T = [_jumps(s, KN) for s in range(64)]
KG_T = [_jumps(s, KG) for s in range(64)]


def attackers_iter(b, sq, by_white):
    """Alle Felder mit Figuren der Farbe by_white, die sq angreifen."""
    P, N, B, R, Q, K = 'PNBRQK' if by_white else 'pnbrqk'
    r, c = divmod(sq, 8)
    pr = r + 1 if by_white else r - 1
    if 0 <= pr < 8:
        for cc in (c - 1, c + 1):
            if 0 <= cc < 8 and b[pr * 8 + cc] == P:
                yield pr * 8 + cc
    for s in KN_T[sq]:
        if b[s] == N:
            yield s
    for s in KG_T[sq]:
        if b[s] == K:
            yield s
    for rays, sl in ((DIAG_R[sq], B), (ORTH_R[sq], R)):
        for ray in rays:
            for s in ray:
                p = b[s]
                if p != '.':
                    if p == sl or p == Q:
                        yield s
                    break


def attackers(b, sq, by_white):
    return list(attackers_iter(b, sq, by_white))


def king_sq(b, white):
    try:
        return b.index('K' if white else 'k')
    except ValueError:
        return -1


def in_check(b, white):
    k = king_sq(b, white)
    return k >= 0 and any(True for _ in attackers_iter(b, k, not white))


def gen_moves(b, white, caps_only=False, chk=None):
    mv = []
    for sq in range(64):
        if chk and sq & 7 == 0:
            chk()
        p = b[sq]
        if p == '.' or p.isupper() != white:
            continue
        t, r, c = p.lower(), sq >> 3, sq & 7
        if t == 'p':
            d = -1 if white else 1
            nr = r + d
            if not 0 <= nr < 8:
                continue
            last = nr == (0 if white else 7)
            if not caps_only or last:
                s = nr * 8 + c
                if b[s] == '.':
                    mv.append((sq, s, last))
                    if r == (6 if white else 1) and b[s + d * 8] == '.':
                        mv.append((sq, s + d * 8, False))
            for cc in (c - 1, c + 1):
                if 0 <= cc < 8:
                    s = nr * 8 + cc
                    q = b[s]
                    if q != '.' and q.isupper() != white and q not in 'Kk':
                        mv.append((sq, s, last))
        elif t in 'nk':
            for s in (KN_T if t == 'n' else KG_T)[sq]:
                q = b[s]
                if q == '.':
                    if not caps_only:
                        mv.append((sq, s, False))
                elif q.isupper() != white and q not in 'Kk':
                    mv.append((sq, s, False))
        else:
            rays = (DIAG_R[sq] if t in 'bq' else []) + (ORTH_R[sq] if t in 'rq' else [])
            for ray in rays:
                for s in ray:
                    q = b[s]
                    if q == '.':
                        if not caps_only:
                            mv.append((sq, s, False))
                        continue
                    if q.isupper() != white and q not in 'Kk':
                        mv.append((sq, s, False))
                    break
    return mv


def make(b, m):
    f, t, pr = m
    nb = b[:]
    p = nb[f]
    nb[t] = ('Q' if p == 'P' else 'q') if pr else p
    nb[f] = '.'
    return nb


def legal_moves(b, white, chk=None):
    out = []
    for m in gen_moves(b, white, chk=chk):
        if chk:
            chk()
        nb = make(b, m)
        k = king_sq(nb, white)
        if k < 0 or not any(True for _ in attackers_iter(nb, k, not white)):
            out.append(m)
    return out


def evaluate(b):
    """Bewertung aus Sicht von Weiß (Centipawns)."""
    s, npm, kings, att = 0, 0, [], []
    for sq, p in enumerate(b):
        if p == '.':
            continue
        t, w = p.lower(), p.isupper()
        r, c = divmod(sq, 8)
        cen = 3 - max(abs(r - 3.5), abs(c - 3.5))
        v = PIECE_VAL[t]
        if t in 'nb':
            v += 8 * cen
            npm += PIECE_VAL[t]
            att.append((sq, t, w))
        elif t == 'p':
            v += 6 * ((6 - r) if w else (r - 1)) + 3 * cen
        elif t == 'q':
            v += 2 * cen
            npm += 900
            att.append((sq, t, w))
        elif t == 'r':
            npm += 500
            att.append((sq, t, w))
        else:
            kings.append((w, cen, sq))
        s += v if w else -v
    if npm <= 2400:  # Endspiel: König zur Mitte
        for w, cen, _ in kings:
            s += 12 * cen if w else -12 * cen
    if MOVER_W and len(kings) == 2:  # Gelerntes: Felder, von denen aus früher Matt gegeben wurde
        ks = {w: sq for w, _, sq in kings}
        for sq, t, w in att:
            kr, kc = divmod(ks[not w], 8)
            r, c = divmod(sq, 8)
            dr, dc = (kr - r if w else r - kr), (c - kc if kc <= 3 else kc - c)
            v = MOVER_W.get((t, dr, dc), 0)
            s += v if w else -v
    return s


class Timeout(Exception):
    pass


class Searcher:
    def __init__(self, deadline, alive):
        self.deadline, self.alive, self.nodes = deadline, alive, 0

    def check(self):
        if time.time() > self.deadline or not self.alive():
            raise Timeout

    def tick(self):
        self.nodes += 1
        if self.nodes & 127 == 0:
            self.check()

    @staticmethod
    def order(b, moves):
        def key(m):
            v = b[m[1]]
            k = PIECE_VAL[v.lower()] * 10 - PIECE_VAL[b[m[0]].lower()] / 10 if v != '.' else 0
            return -(k + (800 if m[2] else 0))
        return sorted(moves, key=key)

    @staticmethod
    def ev(b, white):
        e = evaluate(b)
        return e if white else -e

    def qs(self, b, white, alpha, beta, d):
        self.tick()
        stand = self.ev(b, white)
        if stand >= beta or d == 0:
            return stand
        alpha = max(alpha, stand)
        for m in self.order(b, gen_moves(b, white, True, self.check)):
            sc = -self.qs(make(b, m), not white, -beta, -alpha, d - 1)
            if sc >= beta:
                return sc
            alpha = max(alpha, sc)
        return alpha

    def search(self, b, white, depth, alpha, beta, ply):
        if depth == 0:
            return self.qs(b, white, alpha, beta, 4)
        self.tick()
        moves = legal_moves(b, white, self.check)
        if not moves:
            return -MATE + ply if in_check(b, white) else 0
        best = -INF
        for m in self.order(b, moves):
            self.check()
            sc = -self.search(make(b, m), not white, depth - 1, -beta, -alpha, ply + 1)
            best = max(best, sc)
            alpha = max(alpha, sc)
            if alpha >= beta:
                break
        return best


def best_move(b, white, alive=lambda: True, limit=2.0, maxd=6):
    """Gibt (zug, score, tiefe) zurück oder None, wenn kein legaler Zug existiert."""
    s = Searcher(time.time() + limit, alive)
    moves = legal_moves(b, white, s.check)
    if not moves:
        return None
    ordered = s.order(b, moves)
    best = (ordered[0], 0, 0)
    for d in range(1, maxd + 1):
        try:
            alpha, cur, cur_sc = -INF, None, -INF
            for m in ordered:
                s.check()
                sc = -s.search(make(b, m), not white, d - 1, -INF, -alpha, 1)
                if sc > cur_sc:
                    cur_sc, cur = sc, m
                alpha = max(alpha, sc)
            best = (cur, cur_sc, d)
            ordered.remove(cur)
            ordered.insert(0, cur)
            if abs(cur_sc) > MATE - 100:
                break
        except Timeout:
            break
    return best


def find_threats(b, white):
    """Figuren der Farbe 'white', die real bedroht sind (Schach, ungedeckt
    oder von einer geringerwertigen Figur angegriffen)."""
    out = []
    for sq, p in enumerate(b):
        if p == '.' or p.isupper() != white:
            continue
        att = attackers(b, sq, not white)
        if not att:
            continue
        t = p.lower()
        if t == 'k':
            out.append((sq, att))
            continue
        defended = any(True for _ in attackers_iter(b, sq, white))
        low = min(ATT_VAL[b[a].lower()] for a in att)
        if not defended or low < PIECE_VAL[t]:
            out.append((sq, att))
    return out


def opp_mated(b, opp, n, chk):
    """opp ist am Zug: wird er matt, obwohl Gegner noch n Züge hat?"""
    replies = legal_moves(b, opp, chk)
    if not replies:
        return in_check(b, opp)
    if n == 0:
        return False
    return all(any_mate(make(b, r), not opp, n, chk) for r in replies)


def any_mate(b, white, n, chk):
    for m in legal_moves(b, white, chk):
        chk()
        nb = make(b, m)
        if n == 1 and not in_check(nb, not white):  # letzter Zug muss Schach geben
            continue
        if opp_mated(nb, not white, n - 1, chk):
            return True
    return False


def side_mates(b, white, n, chk):
    out = []
    for m in legal_moves(b, white, chk):
        chk()
        nb = make(b, m)
        if n == 1 and not in_check(nb, not white):
            continue
        if opp_mated(nb, not white, n - 1, chk):
            out.append(m)
    return out


def find_mates(b, white, chk=lambda: None):
    """Kürzeste erzwungene Mattführung in < 3 Zügen: (n, [Erstzüge]) oder None."""
    for n in (1, 2):
        ms = side_mates(b, white, n, chk)
        if ms:
            return n, ms
    return None


def sqname(sq):
    return 'abcdefgh'[sq & 7] + str(8 - (sq >> 3))


def describe(b, m):
    f, t, pr = m
    s = f"{NAME_DE[b[f].lower()]} {sqname(f)} {'×' if b[t] != '.' else '→'} {sqname(t)}"
    return s + (" = Dame" if pr else "")


def fmt_score(sc):
    if abs(sc) > MATE - 100:
        n = (MATE - abs(sc) + 1) // 2
        return f"Matt in {n}" if sc > 0 else f"Matt gegen dich in {n}"
    return f"{sc / 100:+.2f}"


# ───────────── Matt-Suche & Lernen ─────────────
MOVER_W = {}  # (Stückart, dr, dc) -> gelernter Bonus; Position relativ zum gematteten König
MEM_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "matt_gedaechtnis.json")


def has_legal(b, white, chk=None):
    for m in gen_moves(b, white, chk=chk):
        if chk:
            chk()
        nb = make(b, m)
        k = king_sq(nb, white)
        if k < 0 or not any(True for _ in attackers_iter(nb, k, not white)):
            return True
    return False


def is_mated(b, white, chk=None):
    return in_check(b, white) and not has_legal(b, white, chk)


def mate_in_1(b, white, chk=None):
    for m in legal_moves(b, white, chk):
        if chk:
            chk()
        if is_mated(make(b, m), not white, chk):
            return m
    return None


def mate_finals(b, white, n, ms, limit=6, chk=None):
    """Gematte Endstellungen zu den gefundenen Mattführungen (zum Lernen)."""
    out = []
    for m in ms[:3]:
        if chk:
            chk()
        nb = make(b, m)
        if n == 1:
            out.append(nb)
        else:
            for r in legal_moves(nb, not white, chk):
                if chk:
                    chk()
                nb2 = make(nb, r)
                m2 = mate_in_1(nb2, white, chk)
                if m2:
                    out.append(make(nb2, m2))
        if len(out) >= limit:
            break
    return out[:limit]


def canon(sq, ksq, mated_white):
    """Feldposition relativ zum gematteten König, farb- und spiegelunabhängig."""
    r, c = divmod(sq, 8)
    kr, kc = divmod(ksq, 8)
    dr, dc = r - kr, c - kc
    if not mated_white:
        dr = -dr
    if kc > 3:
        dc = -dc
    return dr, dc


def classify(b, k, mated_white, chk):
    kr, kc = divmod(k, 8)
    own = lambda s: b[s] != '.' and b[s].isupper() == mated_white
    if len(chk) >= 2:
        return "Doppelschach-Matt"
    a = chk[0]
    t = b[a].lower()
    if t == 'n' and all(own(s) for s in KG_T[k]):
        return "Erstickungsmatt"
    if kr == (7 if mated_white else 0) and t in 'rq' and (a >> 3) == kr:
        fr = kr - 1 if mated_white else kr + 1
        if all(own(s) for s in KG_T[k] if (s >> 3) == fr):
            return "Grundreihenmatt"
    if t == 'q' and max(abs((a >> 3) - kr), abs((a & 7) - kc)) == 1:
        return "Kontakt-Damenmatt"
    if kr in (0, 7) and kc in (0, 7):
        return "Eckmatt"
    if kr in (0, 7) or kc in (0, 7):
        return "Randmatt"
    return "Matt im Brettinneren"


def signature(b, k, mated_white):
    kr, kc = divmod(k, 8)
    items = []
    for sq, p in enumerate(b):
        if p == '.' or sq == k or max(abs((sq >> 3) - kr), abs((sq & 7) - kc)) > 2:
            continue
        dr, dc = canon(sq, k, mated_white)
        own = p.isupper() == mated_white
        items.append(f"{p.upper() if own else p.lower()}{dr},{dc}")
    return ";".join(sorted(items))


class MateMemory:
    """Merkt sich, wie Matts entstanden sind (Muster, mattgebende Felder) und
    speichert das dauerhaft in matt_gedaechtnis.json."""

    def __init__(self, path=MEM_PATH):
        self.path, self.lock = path, threading.Lock()
        self.d = {"matts": 0, "patterns": {}, "mover": {}, "sigs": {}, "seen": []}
        try:
            with open(path, encoding="utf-8") as f:
                self.d.update(json.load(f))
        except Exception:
            pass
        self.seen = set(self.d["seen"])
        self._weights()

    def _weights(self):
        MOVER_W.clear()
        for key, n in self.d["mover"].items():
            t, dr, dc = key.split(",")
            MOVER_W[(t, int(dr), int(dc))] = min(n, 10) * 2

    def summary(self):
        return {"matts": self.d["matts"], "patterns": self.d["patterns"].copy()}

    def _save(self):
        self.d["seen"] = self.d["seen"][-3000:]
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self.d, f, ensure_ascii=False)
        except OSError:
            pass

    def learn(self, b, mated_white):
        """Lernt aus einer Schachmatt-Stellung. True, wenn sie neu war."""
        k = king_sq(b, mated_white)
        if k < 0 or not is_mated(b, mated_white):
            return False
        h = hashlib.md5((''.join(b) + str(mated_white)).encode()).hexdigest()[:12]
        with self.lock:
            if h in self.seen:
                return False
            self.seen.add(h)
            d = self.d
            d["seen"].append(h)
            chk = attackers(b, k, not mated_white)
            name = classify(b, k, mated_white, chk)
            d["matts"] += 1
            d["patterns"][name] = d["patterns"].get(name, 0) + 1
            for a in chk:
                dr, dc = canon(a, k, mated_white)
                key = f"{b[a].lower()},{dr},{dc}"
                d["mover"][key] = d["mover"].get(key, 0) + 1
            sig = signature(b, k, mated_white)
            if sig in d["sigs"] or len(d["sigs"]) < 800:
                d["sigs"][sig] = d["sigs"].get(sig, 0) + 1
            self._weights()
            self._save()
        return True


def random_endgame(chk=None):
    """Zufälliges Endspiel für das Selbsttraining (Weiß am Zug, klar im Vorteil)."""
    while True:
        if chk:
            chk()
        wset = ['K'] + random.sample(['Q', 'R', 'R', 'B', 'N', 'P'], random.randint(1, 3))
        if not any(p in 'QR' for p in wset):
            wset[1] = 'Q'
        bset = ['k'] + random.sample(['p', 'n', 'b'], random.randint(0, 2))
        pcs = wset + bset
        sqs = random.sample(range(64), len(pcs))
        if any(p in 'Pp' and (s >> 3) in (0, 7) for p, s in zip(pcs, sqs)):
            continue
        wk, bk = sqs[0], sqs[len(wset)]
        if max(abs((wk >> 3) - (bk >> 3)), abs((wk & 7) - (bk & 7))) < 2:
            continue
        b = ['.'] * 64
        for p, s in zip(pcs, sqs):
            b[s] = p
        if not in_check(b, False):
            return b


def swap_colors(b):
    nb = ['.'] * 64
    for sq, p in enumerate(b):
        if p != '.':
            nb[(7 - (sq >> 3)) * 8 + (sq & 7)] = p.swapcase()
    return nb


def _engine_worker(commands, results, generation):
    memory = MateMemory()
    results.put(("memory", 0, memory.summary()))

    while True:
        command = commands.get()
        if command[0] == "stop":
            return
        kind, job = command[:2]
        if generation.value != job:
            continue

        alive = lambda: generation.value == job

        def chk():
            if not alive():
                raise Timeout

        try:
            if kind == "analyze":
                _, _, board, white = command
                board = list(board)
                for color in (True, False):
                    chk()
                    memory.learn(board, color)

                deadline = time.time() + 4

                def mate_check():
                    chk()
                    if time.time() > deadline:
                        raise Timeout

                try:
                    mate = find_mates(board, white, mate_check)
                except Timeout:
                    if not alive():
                        continue
                    mate = None
                name, finals = None, []
                if mate:
                    try:
                        finals = mate_finals(board, white, *mate, chk=mate_check)
                    except Timeout:
                        if not alive():
                            continue
                        finals = []
                    if finals:
                        final = finals[0]
                        k = king_sq(final, not white)
                        name = classify(final, k, not white, attackers(final, k, white))
                        for final in finals:
                            mate_check()
                            memory.learn(final, not white)
                try:
                    best = best_move(board, white, alive=alive)
                except Timeout:
                    if not alive():
                        continue
                    best = None
                if alive():
                    info = (name, memory.d["patterns"].get(name, 0)) if name else None
                    results.put(("analysis", job, mate, info, best, memory.summary()))
            elif kind == "training":
                games = 0
                while alive():
                    board, white = random_endgame(chk), True
                    if random.random() < 0.5:
                        board, white = swap_colors(board), False
                    for _ in range(80):
                        chk()
                        if all(piece in 'Kk.' for piece in board):
                            break
                        result = best_move(board, white, alive=alive, limit=0.12, maxd=4)
                        chk()
                        if result is None:
                            if is_mated(board, white, chk):
                                memory.learn(board, white)
                            break
                        board, white = make(board, result[0]), not white
                    games += 1
                    results.put(("training", job, games, memory.summary()))
        except Timeout:
            continue
        except Exception as exc:
            if alive():
                results.put(("error", job, f"{type(exc).__name__}: {exc}"))


class EngineWorker:
    def __init__(self):
        context = multiprocessing.get_context("spawn")
        self.commands = context.Queue()
        self.results = context.Queue()
        self.generation = context.Value("q", 0)
        self.process = context.Process(
            target=_engine_worker,
            args=(self.commands, self.results, self.generation),
            name="chess-engine",
            daemon=True,
        )
        self.process.start()
        self.closed = False

    def _next_generation(self):
        with self.generation.get_lock():
            self.generation.value += 1
            return self.generation.value

    def invalidate(self):
        return self._next_generation()

    def analyze(self, board, white):
        if self.closed or not self.process.is_alive():
            raise RuntimeError("Analyse-Worker nicht verfügbar")
        job = self._next_generation()
        self.commands.put(("analyze", job, tuple(board), white))
        return job

    def train(self):
        if self.closed or not self.process.is_alive():
            raise RuntimeError("Analyse-Worker nicht verfügbar")
        job = self._next_generation()
        self.commands.put(("training", job))
        return job

    def poll(self):
        while True:
            try:
                message = self.results.get_nowait()
            except queue.Empty:
                return None
            if message[0] == "memory" or message[1] == self.generation.value:
                return message

    def close(self):
        if self.closed:
            return
        self.closed = True
        self._next_generation()
        if self.process.is_alive():
            self.commands.put(("stop",))
            self.process.join(timeout=1)
            if self.process.is_alive():
                self.process.terminate()
                self.process.join(timeout=1)
        self.commands.cancel_join_thread()
        self.results.cancel_join_thread()
        self.commands.close()
        self.results.close()


START = list("rnbqkbnr" + "pppppppp" + "." * 32 + "PPPPPPPP" + "RNBQKBNR")

# ───────────────────────── UI ─────────────────────────
BG, PANEL, BORDER = "#0A1020", "#111B2E", "#263852"
INK, MUTED = "#E8F1FF", "#8293AE"
LIGHT, DARK = "#243650", "#142238"
GREEN, GREEN_L, GREEN_D = "#00E0B0", "#17483F", "#155B58"
RED, RED_L = "#FF5878", "#512638"
BLUE, BLUE_L, BLUE_D = "#53C7FF", "#17415C", "#245D7D"
GLYPH = {'k': '\u265A', 'q': '\u265B', 'r': '\u265C', 'b': '\u265D', 'n': '\u265E', 'p': '\u265F'}
OUT = [(-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (1, 1), (-1, 1), (1, -1)]
S, M, CELL = 72, 24, 68  # Feldgröße, Rand, Palettenzelle


class App:
    def __init__(self, root):
        self.root = root
        root.title("Schach-Analyse")
        root.configure(bg=BG)
        root.resizable(False, False)

        fams = set(tkfont.families())
        fam = next((f for f in ("Segoe UI Symbol", "Apple Symbols", "DejaVu Sans",
                                "Arial Unicode MS", "FreeSerif") if f in fams), "TkDefaultFont")
        self.pf = (fam, -int(S * 0.72))
        self.pf_small = (fam, -int(CELL * 0.72))
        self.ui = "Helvetica"

        self.b = START[:]
        self.side = 'w'
        self.tool = None
        self.drag = None
        self.flip = False
        self.drag_piece = None
        self.pal_piece = None
        self.press_xy = (0, 0)
        self.moved = False
        self.best = None
        self.mate = None
        self.job = 0
        self.worker = EngineWorker()
        self.memory_stats = {"matts": 0, "patterns": {}}
        self.worker_error_shown = False
        self.show_thr = tk.BooleanVar(value=False)
        self.training = False
        self.train_txt = ""

        self._build_top()
        body = tk.Frame(root, bg=BG)
        body.pack(padx=24, pady=(4, 20))

        left = tk.Frame(body, bg=BG)
        left.pack(side="left")
        self.cv = tk.Canvas(left, width=8 * S + 2 * M, height=8 * S + 2 * M,
                            bg=BG, highlightthickness=1, highlightbackground=BORDER)
        self.cv.pack()
        self.lbl_best = tk.Label(left, bg=BG, fg=GREEN, font=(self.ui, 15, "bold"), anchor="w")
        self.lbl_best.pack(fill="x", padx=M, pady=(12, 0))
        self.lbl_mate = tk.Label(left, bg=BG, fg=BLUE, font=(self.ui, 13, "bold"), anchor="w",
                                 justify="left", wraplength=8 * S)
        self.lbl_mate.pack(fill="x", padx=M, pady=(2, 0))
        self.lbl_thr = tk.Label(left, bg=BG, fg=RED, font=(self.ui, 12), anchor="w",
                                justify="left", wraplength=8 * S)
        self.lbl_thr.pack(fill="x", padx=M, pady=(2, 0))

        right = tk.Frame(body, bg=PANEL, highlightbackground=BORDER, highlightthickness=1,
                         padx=16, pady=16)
        right.pack(side="left", padx=(20, 0), anchor="n", pady=M)
        tk.Label(right, text="FIGUREN  /  SETUP", bg=PANEL, fg=BLUE,
                 font=(self.ui, 10, "bold")).pack(anchor="w")
        self.pal = tk.Canvas(right, width=2 * CELL, height=6 * CELL,
                             bg=PANEL, highlightthickness=0)
        self.pal.pack(pady=(6, 12))
        self._button(right, "Brett drehen  ⟲", self.flip_board)
        self.btn_erase = self._button(right, "Entfernen", lambda: self.set_tool('erase'))
        self._button(right, "Grundstellung", lambda: self.load(START[:]))
        self._button(right, "Brett leeren", lambda: self.load(['.'] * 64))
        tk.Label(right, text="LERNEN  /  KI", bg=PANEL, fg=BLUE,
                 font=(self.ui, 10, "bold")).pack(anchor="w", pady=(16, 0))
        self.btn_train = self._button(right, "Matt-Training", self.toggle_train)
        self.lbl_learn = tk.Label(right, bg=PANEL, fg=MUTED, font=(self.ui, 10), justify="left",
                                  anchor="w", wraplength=2 * CELL)
        self.lbl_learn.pack(anchor="w", pady=(6, 0))

        self.pal.bind("<Button-1>", self._pal_press)
        self.pal.bind("<B1-Motion>", self._pal_motion)
        self.pal.bind("<ButtonRelease-1>", self._pal_release)
        self.cv.bind("<Button-1>", self._press)
        self.cv.bind("<B1-Motion>", self._motion)
        self.cv.bind("<ButtonRelease-1>", self._release)
        self.cv.bind("<Button-2>", self._rclick)
        self.cv.bind("<Button-3>", self._rclick)

        root.bind("<f>", lambda e: self.flip_board())
        root.bind("<F>", lambda e: self.flip_board())
        root.protocol("WM_DELETE_WINDOW", self.close)
        self.draw_palette()
        self.refresh()
        self.poll()

    # ── Widgets ──
    def _build_top(self):
        top = tk.Frame(self.root, bg=PANEL, highlightbackground=BORDER, highlightthickness=1)
        top.pack(fill="x", padx=24, pady=(20, 10))
        tk.Label(top, text="ANALYSE  /  ZUG FÜR", bg=PANEL, fg=MUTED,
                 font=(self.ui, 10, "bold")).pack(side="left", padx=(14, 10), pady=12)
        self.tog = {}
        for key, text in (('w', "Weiß"), ('b', "Schwarz")):
            l = tk.Label(top, text=text, font=(self.ui, 11, "bold"), padx=16, pady=6, cursor="hand2")
            l.pack(side="left")
            l.bind("<Button-1>", lambda e, k=key: self.set_side(k))
            self.tog[key] = l
        self._style_toggle()
        tk.Checkbutton(top, text="Drohungen anzeigen", variable=self.show_thr, command=self.draw,
                       bg=PANEL, activebackground=PANEL, fg=INK, activeforeground=BLUE,
                       selectcolor=BG, font=(self.ui, 11),
                       bd=0, highlightthickness=0, cursor="hand2").pack(side="right", padx=14)

    def _button(self, parent, text, cmd):
        l = tk.Label(parent, text=text, bg="#1A2940", fg=INK, font=(self.ui, 11, "bold"),
                     width=14, pady=7, cursor="hand2")
        l.pack(pady=3, fill="x")
        l.bind("<Button-1>", lambda e: cmd())
        l.bind("<Enter>", lambda e: l.configure(bg="#263852") if l is not self.btn_erase or self.tool != 'erase' else None)
        l.bind("<Leave>", lambda e: self._style_erase() if l is self.btn_erase else l.configure(bg="#1A2940"))
        return l

    def _style_toggle(self):
        for k, l in self.tog.items():
            on = k == self.side
            l.configure(bg=GREEN_D if on else PANEL, fg=GREEN if on else MUTED)

    def _style_erase(self):
        self.btn_erase.configure(bg=GREEN_D if self.tool == 'erase' else "#1A2940",
                                 fg=GREEN if self.tool == 'erase' else INK)

    # ── Zustand ──
    def set_side(self, k):
        self.side = k
        self._style_toggle()
        self.refresh()

    def set_tool(self, t):
        self.tool = None if self.tool == t else t
        self._style_erase()
        self.draw_palette()
        self.cv.configure(cursor="crosshair" if self.tool else "arrow")

    def load(self, board):
        self.b = board
        self.refresh()

    def put(self, sq, p):
        if p in 'Pp' and (sq >> 3) in (0, 7):
            return False
        if p in 'Kk' and p in self.b:
            self.b[self.b.index(p)] = '.'
        self.b[sq] = p
        return True

    # ── Eingabe ──
    def _sq(self, x, y):
        c, r = (x - M) // S, (y - M) // S
        if not (0 <= c < 8 and 0 <= r < 8):
            return None
        if self.flip:
            r, c = 7 - r, 7 - c
        return r * 8 + c

    def _disp(self, sq):
        r, c = divmod(sq, 8)
        return (7 - r, 7 - c) if self.flip else (r, c)

    def flip_board(self):
        self.flip = not self.flip
        self.draw()

    def _sq_root(self, e):
        return self._sq(e.x_root - self.cv.winfo_rootx(), e.y_root - self.cv.winfo_rooty())

    def _far(self, e):
        return math.hypot(e.x_root - self.press_xy[0], e.y_root - self.press_xy[1]) >= 5

    def _ghost(self, e):
        self.cv.delete('ghost')
        x, y = e.x_root - self.cv.winfo_rootx(), e.y_root - self.cv.winfo_rooty()
        self.glyph(self.cv, x, y, self.drag_piece, self.pf, 'ghost')

    def _apply_tool(self, sq):
        if self.tool == 'erase':
            self.b[sq] = '.'
        else:
            self.put(sq, self.tool)
        self.refresh()

    # Palette: Klick = Werkzeug wählen, Ziehen = Figur aufs Brett setzen
    def _pal_press(self, e):
        col, row = e.x // CELL, e.y // CELL
        self.pal_piece = None
        if 0 <= col < 2 and 0 <= row < 6:
            t = 'kqrbnp'[row]
            self.pal_piece = t.upper() if col == 0 else t
            self.press_xy, self.moved = (e.x_root, e.y_root), False

    def _pal_motion(self, e):
        if self.pal_piece is None or (not self.moved and not self._far(e)):
            return
        self.moved, self.drag_piece = True, self.pal_piece
        self._ghost(e)

    def _pal_release(self, e):
        p, self.pal_piece = self.pal_piece, None
        if p is None:
            return
        if not self.moved:
            self.set_tool(p)
            return
        self.cv.delete('ghost')
        self.drag_piece = None
        sq = self._sq_root(e)
        if sq is not None and self.put(sq, p):
            self.refresh()

    # Brett: Figur ziehen & loslassen = verschieben; Klick mit Werkzeug = platzieren
    def _press(self, e):
        sq = self._sq(e.x, e.y)
        if sq is None:
            return
        self.press_xy, self.moved = (e.x_root, e.y_root), False
        if self.b[sq] != '.':
            self.drag = sq
        elif self.tool:
            self._apply_tool(sq)

    def _motion(self, e):
        if self.drag is None or (not self.moved and not self._far(e)):
            return
        if not self.moved:
            self.moved, self.drag_piece = True, self.b[self.drag]
            self.draw()  # Originalfigur ausblenden
        self._ghost(e)

    def _release(self, e):
        if self.drag is None:
            return
        src, self.drag = self.drag, None
        self.cv.delete('ghost')
        self.drag_piece = None
        if not self.moved:
            if self.tool:
                self._apply_tool(src)
            return
        sq = self._sq_root(e)
        p = self.b[src]
        if sq is None or sq == src:
            self.draw()
            return
        self.b[src] = '.'
        if not self.put(sq, p):
            self.b[src] = p
        self.refresh()

    def _rclick(self, e):
        sq = self._sq(e.x, e.y)
        if sq is not None and self.b[sq] != '.':
            self.b[sq] = '.'
            self.refresh()

    # ── Analyse ──
    def refresh(self):
        if self.training:
            self.training = False
            self.train_txt = ""
            self.btn_train.configure(text="Matt-Training", fg=INK)
        self.best = self.mate = None
        self.lbl_mate.configure(text="")
        self.update_learn()
        self.lbl_best.configure(text="Berechne …", fg=MUTED)
        self.draw()
        try:
            self.job = self.worker.analyze(self.b[:], self.side == 'w')
        except RuntimeError as exc:
            self.job = self.worker.invalidate()
            self.worker_error_shown = True
            self.lbl_best.configure(text=f"Analyse fehlgeschlagen: {exc}", fg=RED)

    def poll(self):
        while True:
            message = self.worker.poll()
            if message is None:
                break
            self._handle_worker_message(message)
        if not self.worker.process.is_alive() and not self.worker_error_shown:
            self.worker_error_shown = True
            self.lbl_best.configure(text="Analyse-Worker beendet", fg=RED)
        if not self.worker.closed:
            self.root.after(80, self.poll)

    def _handle_worker_message(self, message):
        kind, job, *data = message
        if kind == "memory":
            self.memory_stats = data[0]
            self.update_learn()
            return
        if job != self.job:
            return
        if kind == "analysis":
            mate, info, result, self.memory_stats = data
            self.show_mate(mate, info)
            self.show_result(result)
        elif kind == "training":
            games, self.memory_stats = data
            self.train_txt = f"Training: {games} Partien"
            self.update_learn()
        elif kind == "error":
            self.training = False
            self.train_txt = ""
            self.btn_train.configure(text="Matt-Training", fg=INK)
            self.lbl_best.configure(text=f"Analyse fehlgeschlagen: {data[0]}", fg=RED)
            self.update_learn()

    def show_mate(self, mate, info):
        self.mate = mate
        if mate:
            n, ms = mate
            opp = "Schwarz" if self.side == 'w' else "Weiß"
            moves = "  /  ".join(describe(self.b, m) for m in ms[:3])
            extra = ""
            if info:
                name, k = info
                extra = f" · {name} ({k}× gelernt)" if k else f" · {name} (neues Muster)"
            self.lbl_mate.configure(text=f"Matt in {n} gegen {opp} möglich: {moves}{extra}")
        self.update_learn()
        self.draw()

    def show_result(self, res):
        self.best = res
        white = self.side == 'w'
        if res is None:
            txt = "Schachmatt – kein Zug möglich" if in_check(self.b, white) else "Kein legaler Zug (Patt)"
            self.lbl_best.configure(text=txt, fg=RED)
        else:
            m, sc, _ = res
            self.lbl_best.configure(text=f"{describe(self.b, m)}   ({fmt_score(sc)})", fg=GREEN)
        self.draw()

    def update_learn(self):
        n, pats = self.memory_stats["matts"], self.memory_stats["patterns"]
        if n:
            top, cnt = max(pats.items(), key=lambda kv: kv[1])
            txt = f"Gelernt: {n} Matts\nHäufigstes: {top} ({cnt}×)"
        else:
            txt = "Noch keine Matts gelernt"
        if self.training and self.train_txt:
            txt += "\n" + self.train_txt
        self.lbl_learn.configure(text=txt)

    def toggle_train(self):
        self.training = not self.training
        self.btn_train.configure(text="Stopp ■" if self.training else "Matt-Training",
                                 fg=RED if self.training else INK)
        if self.training:
            self.train_txt = "Training läuft …"
            try:
                self.job = self.worker.train()
                self.lbl_best.configure(text="Matt-Training läuft …", fg=MUTED)
            except RuntimeError as exc:
                self.training = False
                self.job = self.worker.invalidate()
                self.btn_train.configure(text="Matt-Training", fg=INK)
                self.lbl_best.configure(text=f"Training fehlgeschlagen: {exc}", fg=RED)
        else:
            self.train_txt = ""
            self.refresh()
        self.update_learn()

    def close(self):
        self.worker.close()
        self.root.destroy()

    # ── Zeichnen ──
    def glyph(self, cv, x, y, p, font, tag=''):
        ch = GLYPH[p.lower()] + '\ufe0e'
        if p.isupper():
            for dx, dy in OUT:
                cv.create_text(x + dx, y + dy, text=ch, font=font, fill="#0A1020", tags=tag)
            cv.create_text(x, y, text=ch, font=font, fill="#F3F8FF", tags=tag)
        else:
            cv.create_text(x, y, text=ch, font=font, fill="#91B4D8", tags=tag)

    def draw_palette(self):
        self.pal.delete('all')
        for row, t in enumerate('kqrbnp'):
            for col, p in enumerate((t.upper(), t)):
                x0, y0 = col * CELL, row * CELL
                sel = self.tool == p
                self.pal.create_rectangle(x0 + 3, y0 + 3, x0 + CELL - 3, y0 + CELL - 3,
                                          fill=GREEN_D if sel else "#1A2940",
                                          outline=GREEN if sel else "#1A2940", width=2)
                self.glyph(self.pal, x0 + CELL / 2, y0 + CELL / 2, p, self.pf_small)

    def _center(self, sq):
        r, c = self._disp(sq)
        return M + c * S + S / 2, M + r * S + S / 2

    def _arrow(self, a, b, color, w, dash=None, trim=(14, 6)):
        x1, y1 = self._center(a)
        x2, y2 = self._center(b)
        d = math.hypot(x2 - x1, y2 - y1) or 1
        ux, uy = (x2 - x1) / d, (y2 - y1) / d
        self.cv.create_line(x1 + ux * trim[0], y1 + uy * trim[0], x2 - ux * trim[1], y2 - uy * trim[1],
                            fill=color, width=w, arrow=tk.LAST, dash=dash,
                            arrowshape=(w * 2, w * 2.3, w), capstyle=tk.ROUND)

    def draw(self):
        cv = self.cv
        cv.delete('all')
        white = self.side == 'w'
        thr = find_threats(self.b, white) if self.show_thr.get() else []
        thr_sq = {t for t, _ in thr}
        mv = self.best[0] if self.best else None
        c_from, c_to = (BLUE_L, BLUE_D) if mv and self.mate and mv in self.mate[1][:6] else (GREEN_L, GREEN_D)

        for sq in range(64):
            r, c = self._disp(sq)
            x, y = M + c * S, M + r * S
            col = LIGHT if (r + c) % 2 == 0 else DARK
            if mv and sq == mv[0]:
                col = c_from
            elif mv and sq == mv[1]:
                col = c_to
            if sq in thr_sq:
                col = RED_L
            cv.create_rectangle(x, y, x + S, y + S, fill=col, outline=col)
            if sq in thr_sq:
                cv.create_rectangle(x + 2, y + 2, x + S - 2, y + S - 2, outline=RED, width=3)
        for i in range(8):
            cv.create_text(M + i * S + S / 2, M + 8 * S + 11, text='abcdefgh'[7 - i if self.flip else i], fill=MUTED, font=(self.ui, 10))
            cv.create_text(M - 12, M + i * S + S / 2, text=str(i + 1 if self.flip else 8 - i), fill=MUTED, font=(self.ui, 10))
        for sq, p in enumerate(self.b):
            if p != '.' and not (self.drag == sq and self.moved):
                self.glyph(cv, *self._center(sq), p, self.pf)

        for t, atts in thr:
            for a in atts:
                self._arrow(a, t, RED, 3, dash=(6, 4), trim=(22, 18))
        mates = self.mate[1][:6] if self.mate else []
        if mv and mv not in mates:
            self._arrow(mv[0], mv[1], GREEN, 9, trim=(20, 4))
        for m in mates:
            self._arrow(m[0], m[1], BLUE, 9, trim=(20, 4))

        if self.show_thr.get():
            if thr:
                names = ", ".join(f"{NAME_DE[self.b[t].lower()]} {sqname(t)}" for t, _ in thr)
                self.lbl_thr.configure(text=f"Bedroht: {names}", fg=RED)
            else:
                self.lbl_thr.configure(text="Keine Drohungen gegen diese Farbe", fg=MUTED)
        else:
            self.lbl_thr.configure(text="")


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()