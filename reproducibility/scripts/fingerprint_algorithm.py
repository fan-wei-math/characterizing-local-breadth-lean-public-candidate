"""Pure canonical fingerprint parse/closure/check algorithm; no approval lifecycle mutation."""
import hashlib
_AUTO=set()

def parse(out):
    """{key: (kind, own, [deps])}, or raise if the Lean side did not run to completion or two
    declarations produced the same key. Records which keys are auto-generated in _AUTO."""
    table, count, auto, dup = {}, None, set(), []
    for line in out.splitlines():
        parts = line.split("\t")
        if parts[0] == "FP" and len(parts) == 6:
            if parts[1] in table:
                dup.append(parts[1])
            table[parts[1]] = (parts[2], parts[4], [d for d in parts[5].split(",") if d])
            if parts[3] == "auto":
                auto.add(parts[1])
        elif parts[0] == "FPCOUNT":
            count = int(parts[1])
    if dup:
        raise RuntimeError(f"two declarations share a fingerprint key: {sorted(set(dup))[:5]}")
    if count is None or count != len(table):
        raise RuntimeError("fingerprint run did not complete (no or mismatched FPCOUNT):\n" + out[-3000:])
    _AUTO.clear(); _AUTO.update(auto)
    return table

def closure_fps(table):
    """{name: fp} -- own hash plus own hashes of the transitive project-local closure."""
    fps = {}
    for n in table:
        seen, stack = set(), [n]
        while stack:
            m = stack.pop()
            if m in seen or m not in table:
                continue
            seen.add(m)
            stack.extend(table[m][2])
        h = hashlib.sha256()
        for m in sorted(seen):
            h.update(f"{m}\t{table[m][0]}\t{table[m][1]}\n".encode())
        fps[n] = h.hexdigest()[:16]
    return fps

def check(approved, current):
    """[(name, problem)] for every approved item that changed or vanished."""
    bad = []
    for n, fp in sorted(approved.items()):
        cur = current.get(n)
        if cur is None:
            bad.append((n, "vanished (renamed or deleted)"))
        elif cur != fp:
            bad.append((n, "changed: its statement, or a definition it is stated in terms of"))
    return bad
