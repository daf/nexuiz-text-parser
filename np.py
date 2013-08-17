#!/usr/bin/env python

import sys, re
from collections import defaultdict
from itertools import groupby, chain
from json import JSONEncoder, dumps
import operator

ignores = ["Server using port",
           "Server listening on address",
           "Loading csprogs.dat",
           "server detected csqc progs",
           "Compressing csprogs.dat",
           "Deflated:",
           "Saving persistent data",
           "done!",
           "Mod_Q3BSP_LoadFaces",
           "Tuba awaits you... not",
           "Sys_DoubleTime",
           ":labels:",
           ":player:",
           ":end",
           ":scores:",
           "\"fraglimit\" changed to",
           "\"timelimit\" changed to"]

rtime = re.compile("=* Log started \((.*)\)")
rwin  = re.compile("(.*) wins")

rstates = {
    'rconnected': re.compile("(.*) connected"),
    'rspec': re.compile("(.*) is spectating now"),
    'rplaying': re.compile("(.*) is playing now"),
    'rchat': re.compile("(.*): .*$"),
    'rfirst': re.compile("(.*) drew first blood"),
    'rstreak': re.compile("(.*) has (\d+) frags in a row"),
    'rstreakend': re.compile("(.*)'s (\d+) kill spree was ended by (.*)"),
    'rstreakendsuicide': re.compile("(.*) ended it all after a (\d+) kill spree"),
    'rtriple': re.compile("(.*) made a TRIPLE FRAG"),
    'rrage': re.compile("(.*) unleashes RAGE"),
    'rmassacre': re.compile("(.*) starts the MASSACRE"),
    'rmayhem': re.compile("(.*) executes MAYHEM!"),
    'rdropped': re.compile("Client \"(.*)\" dropped"),
    'rdisconnected': re.compile("(.*) disconnected")
}

rkills = {
    'shotgun': re.compile("(.*) was gunned by (.*)"),
    'machinegun': re.compile("(.*) was riddled full of holes by (.*)"),
    'nex': re.compile("(.*) was sniped by (.*)|(.*) has been vaporized by (.*)"),
    'crylink': re.compile("(.*) could not hide from (.*)'s Crylink|(.*) took a close look at (.*)'s Crylink|(.*) was too close to (.*)'s Crylink"),
    'rocket': re.compile("(.*) almost dodged (.*)'s rocket|(.*) ate (.*)'s rocket|(.*) hoped (.*)'s missiles wouldn't bounce"),
    'blue': re.compile("(.*) got too close to (.*)'s blue beam|(.*) was blasted by (.*)'s blue beam|(.*) got in touch with (.*)'s blue ball"),
    'bluecombo': re.compile("(.*) felt the electrifying air of (.*)'s combo"),
    'grenade': re.compile("(.*) almost dodged (.*)'s grenade|(.*) ate (.*)'s grenade"),
    'telefrag': re.compile("(.*) was telefragged by (.*)"),
    'pummel': re.compile("(.*) was pummeled by (.*)"),
    'grounded': re.compile("(.*) was grounded by (.*)"),
    'slimed': re.compile("(.*) was slimed by (.*)"),
    'lava': re.compile("(.*) was cooked by (.*)"),
    'bounds': re.compile("(.*) was thrown into a world of hurt by (.*)"),
}

rsuicides = {
    'detonated': re.compile("(.*) detonated"),
    'plasma': re.compile("(.*) played with plasma|(.*) could not remember where he put plasma"),
    'rocket': re.compile("(.*) played with tiny rockets"),
    'slimed': re.compile("(.*) was slimed"),
    'crylink': re.compile("(.*) succeeded at self-destructing himself with the Crylink"),
    'explode': re.compile("(.*) exploded"),
    'bounds': re.compile("(.*) was in the wrong place"),
    'fall': re.compile("(.*) hit the ground with a crunch"),
}

# player dict:
    # username: name
    # lives: []     # list of lists, each successful kill before own death
    # kills: {}     # user -> number
    # deaths: {}    # user -> number
    # suicides: number

class Player(dict):
    def __init__(self):
        self['lives'] = []
        self['kills'] = defaultdict(int)
        self['deaths'] = defaultdict(int)
        self['suicides'] = 0
        self['curlife'] = []    # list of players killed this current life, to be added to lives on death or match end?

    def push_curlife(self):
        self['lives'].append(self['curlife'])
        self['curlife'] = []

class Match(dict):
    def __init__(self):
        self['gametime'] = None
        self['scoreboard'] = []
        self['players'] = defaultdict(Player)
        self['weapons'] = defaultdict(list) # weapon -> [(killer, killed), ...]

def finish_game(curmatch, matches, last_time):
    if curmatch is not None and len(curmatch['scoreboard']):

        if last_time is not None:
            curmatch['gametime'] = last_time

        curmatch['players'] = dict(curmatch['players'])

        # push all ending lives, convert dicts
        for p in curmatch['players'].itervalues():
            p.push_curlife()

            p['kills'] = dict(p['kills'])
            p['deaths'] = dict(p['deaths'])

        # calc scoreboard
        board = []
        for name, player in curmatch['players'].iteritems():
            sc = Score()
            sc.name     = name
            sc.kills    = sum(player['kills'].itervalues())
            sc.deaths   = sum(player['deaths'].itervalues())
            sc.suicides = player['suicides']

            board.append(sc)

        # build pvp for this match

        keyfunc = lambda x: x.name
        # dict of name -> [Scores vs each player, sorted by score?]
        pvp = defaultdict(list)
        for name, player in curmatch['players'].iteritems():
            # translate into Scores

            # turn into defaultdicts for easier access
            kills = defaultdict(int, player['kills'])
            deaths = defaultdict(int, player['deaths'])

            # get all people we've killed or been killed by
            opponents = set()
            map(opponents.add, player['deaths'])
            map(opponents.add, player['kills'])

            for opp in opponents:
                sc = Score()
                sc.name = opp
                sc.kills = kills[opp]
                sc.deaths = deaths[opp]

                pvp[name].append(sc)

        # now sort and aggregate pvp
        for name in pvp.keys():
            scorelist = sorted(pvp[name], key=keyfunc)
            scorelist = sorted([sum(v, Score()) for k, v in groupby(scorelist, keyfunc)], reverse=True)

            pvp[name] = scorelist

        curmatch['pvp'] = dict(pvp)

        # assemble weapons stats for this match

        # dict of name -> weapon -> Score(kills with, died by, suicides?)
        weapons_by_name = defaultdict(lambda: defaultdict(Score))

        # dict of weapon -> Score (only kills / suicides -- deaths are always symmetrical to kills)
        weapons_agg = defaultdict(Score)

        for weapon, kills in curmatch['weapons'].iteritems():
            for k in kills:
                if len(k) == 2:
                    weapons_by_name[k[0]][weapon].kills += 1
                    weapons_by_name[k[1]][weapon].deaths += 1

                    weapons_agg[weapon].kills += 1
                else:
                    # 1-tuple means suicide!
                    weapons_by_name[k[0]][weapon].suicides += 1
                    weapons_agg[weapon].suicides += 1

        # translate back to dicts
        for name in weapons_by_name.keys():
            weapons_by_name[name] = dict(weapons_by_name[name])

        weapons_by_name = dict(weapons_by_name)
        weapons_agg = dict(weapons_agg)

        curmatch['weapons_by_name'] = weapons_by_name
        curmatch['weapons_agg']     = weapons_agg
        del curmatch['weapons']

        curmatch['leaderboard'] = sorted(board, reverse=True)
        matches.append(curmatch)

    return Match()

def parse_log(log_file):

    matches = []

    with open(log_file) as f:
        lines = f.readlines()

    last_time = None

    curmatch = finish_game(None, matches, last_time)
    rcolors = re.compile("\^.")

    for idx, l in enumerate(lines):
        l = rcolors.sub("", l.strip()).replace("\x05", "")
        for i in ignores:
            if i in l:
                break
        else:
            m = rtime.search(l)
            if m:
                curmatch = finish_game(curmatch, matches, last_time)
                #print "GAME START"
                curmatch['gametime'] = m.groups()[0]
                last_time = m.groups()[0]
                continue

            m = rwin.search(l)
            if m:
                curmatch = finish_game(curmatch, matches, last_time)
                continue

            for lbl, r in rstates.iteritems():
                m = r.search(l)
                if m:
                    #print "MATCH", lbl, l
                    break
            else:

                for weapon, r in rkills.iteritems():
                    m = r.search(l)
                    if m:
                        killed, killer = filter(None, m.groups())
                        #print "KILL", killer, killed, weapon

                        # update killer
                        curmatch['players'][killer]['kills'][killed] += 1
                        curmatch['players'][killer]['curlife'].append(killed)

                        # update killed
                        curmatch['players'][killed]['deaths'][killer] += 1
                        curmatch['players'][killed].push_curlife()

                        # update weapons
                        curmatch['weapons'][weapon].append((killer, killed))

                        # update scoreboard
                        curmatch['scoreboard'].append([(killer, 1, 0, 0, weapon),
                                                       (killed, 0, 1, 0, weapon)])

                        break
                else:
                    for lbl, r in rsuicides.iteritems():
                        m = r.search(l)
                        if m:
                            killed = filter(None, m.groups())[0]

                            # updated killed
                            curmatch['players'][killed]['suicides'] += 1
                            curmatch['players'][killed].push_curlife()

                            # update weapons with a 1-tuple to indicate suicide
                            curmatch['weapons'][lbl].append((killed,))

                            # update scoreboard
                            curmatch['scoreboard'].append([(killed, 0, 0, 1, lbl)])

                            break
                    else:
                        print >>sys.stderr, "UNKNOWN LINE", idx, l

    return matches

class Score(object):
    def __init__(self):
        self.name = None
        self.kills = 0
        self.deaths = 0
        self.suicides = 0
        self.matches = 1

    @property
    def score(self):
        return self.kills - self.suicides

    @property
    def kdr(self):
        if self.deaths == 0:
            if self.kills == 0:
                return 0
            else:
                return float("inf")

        return self.kills / float(self.deaths)

    def __add__(self, other):
        sc = Score()
        sc.name     = self.name or other.name
        sc.kills    = self.kills + other.kills
        sc.deaths   = self.deaths + other.deaths
        sc.suicides = self.suicides + other.suicides
        sc.matches  = self.matches + other.matches

        return sc

    def __cmp__(self, other):
        if self.score == other.score:
            if self.kills == other.kills:
                if self.suicides == other.suicides:
                    return cmp(self.deaths, other.deaths)
                else:
                    return cmp(self.suicides, other.suicides)
            else:
                return cmp(self.kills, other.kills)
        else:
            return cmp(self.score, other.score)

    def __repr__(self):
        return "%15s %4d %4d %4d %4d %6.2f (%4d)" % (self.name, self.score, self.kills, self.deaths, self.suicides, self.kdr, self.matches)

def scoreboard(scoreboard, players=None):
    """
    Parses a changelog style scoreboard into a sorted one.

    Pass a subset if you want up to X events.

    This probably isn't used.
    """
    players = players or []
    player_set = set(players)

    by_player = defaultdict(Score)

    for scoreline in scoreboard:
        for line in scoreline:
            sc = by_player[line[0]]

            sc.name = line[0]
            sc.kills += line[1]
            sc.deaths += line[2]
            sc.suicides += line[3]

    board = sorted(by_player.values(), reverse=True)
    return board

def aggregate(matches):
    """
    Get totals for leaderboards, PvP, weapons.
    """
    boards = []
    map(boards.extend, [x['leaderboard'] for x in matches])

    keyfunc = lambda x: x.name
    boards = sorted(boards, key=keyfunc)
    boards = sorted([sum(v, Score()) for k,v in groupby(boards, keyfunc)], reverse=True)

    pvp = defaultdict(list)
    for m in matches:
        for name, opps in m['pvp'].iteritems():
            pvp[name].extend(opps)

    # sort each one
    for name in pvp.iterkeys():
        pvp[name] = sorted(pvp[name], key=keyfunc)

    # groupby and summary
    for name in pvp.iterkeys():
        pvp[name] = [reduce(operator.add, v) for _,v in groupby(pvp[name], keyfunc)]

    pvp = dict(pvp)

    # weapons
    c = chain(*(m['weapons_by_name'].items() for m in matches))
    weapons_by_name = sorted(c, key=operator.itemgetter(0))
    weapons_by_name = {k:[vv[1] for vv in v] for k, v in groupby(weapons_by_name, operator.itemgetter(0))}

    # now iterate each person and aggregate each of their weapon match records
    for name in weapons_by_name:
        c = chain(*(w.items() for w in weapons_by_name[name]))
        player_weapons = sorted(c, key=operator.itemgetter(0))
        player_weapons = {k:reduce(operator.add, [vv[1] for vv in v]) for k, v in groupby(player_weapons, operator.itemgetter(0))}

        weapons_by_name[name] = player_weapons

    # now to aggregate all weapon stats just do same join process with values
    c = chain(*(w.items() for w in weapons_by_name.itervalues()))
    weapons_agg = sorted(c, key=operator.itemgetter(0))
    weapons_agg = {k:reduce(operator.add, [vv[1] for vv in v]) for k, v in groupby(weapons_agg, operator.itemgetter(0))}

    return {'leaderboard':boards,
            'pvp':dict(pvp),
            'weapons_by_name':weapons_by_name,
            'weapons_agg':weapons_agg}

if __name__ == "__main__":
    matches = parse_log(sys.argv[1])
    agg = aggregate(matches)

    class DefaultEncoder(JSONEncoder):
        def default(self, o):
            return o.__dict__

    print dumps({'matches':matches, 'aggregate':agg}, cls=DefaultEncoder, indent=2)




