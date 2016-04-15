import sys
import json

sep = "__"

def symbol(s, t):
    return {"id": s, "t": t}

def readGrammar(fname):
    with open(fname, "r") as f:
        n = f.readline().strip()
        g = json.load(f)
        return (n, g)

def genLMap(g):
    ruleList = ["L0"]
    lmap = []
    for lhs, alts in g.items():
        ruleList.append("L" + sep + lhs)
        curr_nt = "L" + sep + lhs + sep
        for i in xrange(len(alts)):
            curr_alt = curr_nt + str(i) + sep
            ruleList.append(curr_alt + "0")
            counter = 1
            for j in xrange(len(alts[i])):
                sym = alts[i][j]
                if sym["t"] == "NT": # Nonterminal, add rule to return to
                    lbl = curr_alt + str(counter)
                    ruleList.append(lbl)
                    lmap.append((lbl, lhs, alts[i][:(j+1)], alts[i][(j+1):]))
                    counter += 1
    return (ruleList, lmap)

def formatList(l):
    return "[" + ",".join(l) + "]"

def formatSymList(a):
    alist = [sym["t"] + ' "' + sym["id"] + '"' for sym in a]
    return formatList(alist)

def formatGrammar(g):
    prodlist = []
    for lhs, alts in g.items():
        altlist = []
        for alt in alts:
            altlist.append(formatSymList(alt))
        prodlist.append("(NT '" + lhs + "',S.fromList " + formatList(altlist) + ")")
    return "H.fromList " + formatList(prodlist)

def formatLMap(lm):
    lmlist = []
    for lbl, lhs, a, b in lm:
        astr = formatSymList(a)
        bstr = formatSymList(b)
        lmlist.append('("' + lbl + '",(NT "' + lhs + '",' + astr + ',' + bstr + '))')
    return "H.fromList " + formatList(lmlist)

def formatFunc(rl, n):
    flist = ['("' + lbl + '",(' + n + lbl + '))' for lbl in rl]
    return "H.fromList " + formatList(flist)

def formatL0(n, gf):
    return """\
{0}L0 _ inp ax st =
    let (l, st') = popQueue st
     in if l /= "" then ({1} l) inp ax st' else st'""".format(n, gf)

def genSets(g):
    firsts = {nt: set() for nt in g}

    def first(s):
        if s == []:
            return {""}
        elif s[0]["t"] == "T":
            return {s[0]["id"]}
        elif "" in firsts[s[0]["id"]]:
            return first(s[1:])
        else:
            return firsts[s[0]]

    changed = True
    while changed:
        changed = False
        for nt, alts in g.items():
            new = set.union(*[first(alt) for alt in alts])
            if new != firsts[nt]:
                changed = True
                firsts[nt] = new

    follows = {nt: set() for nt in g}
    follows["S"] = {"$"} # S must be the start symbol, $ is eof

    mark = {}
    for nt, alts in g.items():
        for alt in alts:
            if alt == []: continue

            for i in xrange(len(alt) - 1):
                if alt[i]["t"] == "NT":
                    curr = alt[i]["id"]
                    fol = first(alt[(i + 1):])
                    if "" in fol:
                        mark[curr].add(nt)
                    follows[curr].update(fol.difference({""}))
            
            if alt[-1]["t"] == "NT":
                mark[alt[-1]["nt"]].add(nt)

    changed = True
    while changed:
        changed = False
        for nt, ls in mark.items():
            new = follows[nt].union(*[follows[ntn] for ntn in ls])
            if new != follows[nt]:
                changed = True
                follows[nt] = new

    return (firsts, follows)

def genAlternateSelect(nt, alist, n):
    # nt = nonterminal string
    # alist = [[grammar symbols]] (list of alternates)
    pre = n + "L" + sep + nt


name, grammar = readGrammar(sys.argv[1])
rlist, lmap = genLMap(grammar)
print formatGrammar(grammar)
print formatLMap(lmap)
print formatFunc(rlist, name)
print formatL0(name, name + "GetFunc")
print genSets(grammar)
