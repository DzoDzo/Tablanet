#idea, karta e 3/52 poeni
#vred karta buja, i posle dict za klk vredat?
#[ime,vrednost], ime za chtkost i guess, i posle pri proverka na kartiso znaame oti se pominale, samo trgnash [0] so gi znaa
#faktichki pair da chuvam [ime,vrednost]
#shuffle, pa cut, pa player knows
#mora a i table da ima, new round da srede mozhi,
#dictionary od vrednosti pr, 14:king, 12:7ka i 5ka, ama ima maka, taa so 2 i 7 plus 2 3 4,idea, da bide lista, i po presmetka na vrednost da vide koo da zema, mozhiii
#dokumentacija ng bitno so kak prava, kak e organizarano, po objekti i po funckii ke se sredea
#idea, na zimane dodaj poeni, if zemani neli points, dodaj points, mosh maalc glomazno do dusha ke se razmilse
#da upraam kombinaciii, i known nekak da sredam, idea, lista so 14 elementi, broj pominani od karta na taj index
#u vrednuvachka funckija ke gledame ako dodadam taa vred na vekje izgenerirante, kakvi mozno ke izl, i klk poeni ke se ostavat na maasta
#da onevozmozham pismo na prva raka, poslednite karti da odat na last taken
#mozhe ng da se oslozhne, dali da zemash poslabo znaejki mozhe da ti se otvore shansa za povekje, ke se izmislee
#tva binarnoto u knapsack da go smenam radi luda slozhenost?
#known da sredame
#mpzhi da se srede evaluete combos funckcija. iliii generate combinations da se proshire, ima maki povrzano so tva ama ke se srede
#mutable da gi narpaame last_taken i first hand
#first hand ke harkdoirame malce nee maka, pa i last taken
#imam da sredam last turn u utility, ako deck e prazen ex = vrednost karti, da vidam count_points so prava ak ne e na prazen deck i to, drte isto taka mozhi da se sredat i kutka
#fixo u generatepoints, mashalaebate aklo
# ka vrakjam state na opponento kartite da se none da daa
#site proverki za posledna raka da mi se onovat na eden player dali ima len 0
#idea, nepoznatio player da go ispolname so gjubre vrednosti i od nih da namalvame
from __future__ import annotations

import copy
import math
import random
#SEED = 12345
#random.seed(SEED)
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations
from typing import Any, Iterable, List, Tuple, Protocol, Optional, Literal, Dict

def get_bit(n, k):
    return (n >> k) & 1 #pomoshna za kombinations
def set_bit_indices(n: int): #brza nachin za naogjanje na bitvoi so 1 vrednost
    idxs = []
    while n:
        lsb = n & -n                  # isolate lowest 1-bit
        idxs.append(lsb.bit_length() - 1)
        n ^= lsb                      # clear that bit
    return idxs
# listac_eq12_2 = [
#     [('9 baklava', 9), ('A detelina', 1), ('A list', 1), ('A srce', 1)],  # 9+1+1+1
#     [('7 list', 7), ('3 srce', 3), ('2 detelina', 2)],                    # 7+3+2
#     [('10 baklava', 10), ('2 srce', 2)],                                  # 10+2
#     [('4 detelina', 4), ('4 list', 4), ('4 srce', 4)],                    # 4+4+4
# ]
def can_merge_without_overlap(listac,ids):
    """True iff the selected combos can be merged with no duplicate cards."""
    seen = set()
    for i in ids:
        for card in listac[i]:
            if card in seen:
                return False
            seen.add(card)
    return True
def possible_takes(listac): #[[(),()],[()],[()]] vaj format se prima, pak isto so binarnite so go ebam
    #print("possible_takes gets",listac)
    viable_combos=[]
    n = len(listac)
    z = 0  # tuka ke zapishuvam koi od takvoto se probani
    MASK = (1 << n) - 1
    for i in range(int(MASK)): #znachi probuvame site mozni
        z+=1
        ids=set_bit_indices(z)
        if len(ids)==1:
            viable_combos.append(listac[ids[0]])
        else:
            if can_merge_without_overlap(listac,ids): #ako mozhame da gi mergename
                viable_combos.append([card for idx in sorted(ids) for card in listac[idx]])
    viable_combos.insert(0,[])
    viable_combos.sort(key=score_combo,reverse=True)
    #print("viable combos",viable_combos)
    return viable_combos
def generate_possible(cards): #cards se tii na table
    #ako gi sortiram, worst case , 1 2 3 4 5 6 7 8 9 10 12 13 14, male i kec treba kak 11 i 1 da se glede, 3 fors idea utre piti chat gpt
    #dict{value:indexi na karti}
    #dict{value:indexi na karti}
    #na krajta na listata da stavam najvrednata kombinacija
    #lista od index na karti uredu
    #da go reworkname,da chuva vrednost: [[imina na karti],[imina na karti]]
    n=len(cards)
    z=0 #tuka ke zapishuvam koi od takvoto se probani
    MASK=(1<<n)-1 #& so tva i dobivam baran broj vrednosti, isto taka od 0 do so ke odame
    combinations = defaultdict(list)
    #za so kec, izbirash situacija dek so eden od nih e 11 samo ednash i posle redovno, i posle dvete sumi gi razgleduvash, Ba si mamata kak ke debagiram ama aj, chatgpt da ti srede raka kak od gornite
    for i in range(int(MASK)):
        z+=1
        ids=set_bit_indices(z)
        card_combo=[cards[idx] for idx in ids]
        #print("looking at cards ",card_combo)
        suma=0
        sumA=0
        first_ace=False
        for index in ids:#ids na cards na table so gi razgleduvame, ako ima vred 1 ke proba so 1 prvo, posle so 11, else redovno

            if cards[index][1]==1 and first_ace==False:
                first_ace=True
                sumA+=11
            else:
                sumA+=cards[index][1]
            suma+=cards[index][1]  #sumire site dek so bitovte se 1
        if suma<15:
            combinations[suma].append(card_combo) #ak e validno dodava vrednost so tii sumi tamka
        if first_ace==True and sumA<15:
            combinations[sumA].append(card_combo)
    for k in combinations:
        combinations[k].sort(key=score_combo,reverse=True)
    #print(combinations)
    return combinations
# ---- Game API (implement these for your game state) ----


class Game(Protocol):
    #da se resham za state i guess, cache maki da upravam, jel moguche to da e to, e moguchee i guess
    #od state mi treba players, table, known, pisma
    #state=([players cards], turn,[deck],[table cards],[known],[taken],[br_pisma],last_taken,phase) phase e za da znam koga e redno random koga ne
    def is_terminal(self, state: Any) -> bool:

        suma=0
        players_s=state[0]
        for player in players_s:
            suma+=len(player)
        if suma==0:
            #print("State is terminal for ",players_s)
            return True
        return False
    def utility(self, state: Any) -> float:
        """Value from MAX's perspective at terminal or when using a heuristic cutoff."""
        #tuka treba razlika u poeni, plus se so ima na table vrednosta*verojatnosta da ja zema, znachi i deck treba
        #da vrateme klk vrede na igracho bez None, i dole proverka, ak e None na red odzimame hevristika a ak ne e dodavame

        taken_s=list(state[5])
        pisma=state[6]
        table_s=state[3]
        known_s=copy.deepcopy(state[4])
        known_s=list(known_s)
        deck_s=copy.deepcopy(state[2])
        turn=state[1]
        players_s=copy.deepcopy(state[0])
        last_taken_s=state[7]

        #print(players_s)
        #print()
        for card in players_s[turn]: #znaa site so znaat+negovite
            if card is not None:
                if card[0] == "2 detelina" or card[0] == "10 baklava":
                    known_s[card[1]] += 0.5  # site so gi znaat,
                else:
                    known_s[card[1]] += 1
        #print(taken_s)
        points=count_points(taken_s)
        points[0]+=pisma[0]
        points[1]+=pisma[1]
        #tuka da imam funkcija so naogje najvredni kombinacii
        #print(table_s)
        combinations=generate_possible(table_s)
        #print(combinations)
        #print(generate_possible(table_s))

        ex=0
       #(players_s)
        opp_m = len(players_s[turn ^ 1]) if len(players_s) > 1 else 0 #drugio klk karti ima u rakta
        #if  math.modf(known_s[2])[0]==0.5:
        total_cards_left = 52-sum(math.ceil(x) for x in known_s) #kolku karti imat pominato
        hyper=0
        hyper_geom=0
        #print("the deck is",len(deck_s))
        if len(deck_s)>0:
            for value in combinations:
                if len(combinations[value])==-0:
                    continue
                #tuka treba nogo da mislam,stoj ke upraame
                most_valuable=combinations[value][0] #tuka beshe possible takes ama nogo bavno u pichko materino, tva i generate da gi napravam po efikasni mosh treba
                                                                    # za taa vrednost (1,..14) najvrednata kombinacija karti so mozhe da se zema
                #print("najvredno is",most_valuable)

                score = score_combo(most_valuable) #da dodame vrednost na karta
                if value in [1,10,12,13,14]:
                    score+=1
                if (len(most_valuable) == len(table_s)):
                    score += 1
                if (value != 2 or value == 2 and math.modf(known_s[2])[0] == 0.5) and (value != 10 or value == 10 and math.modf(known_s[10])[0] == 0.5): #ako ne e 2 ili e 2 ama pominana e lichna dovjka, i ako ne e 10 ili e 10 ama pominana e lichna desetka
                    cards_left= 4 - math.ceil(known_s[value]) #klk se ostanani
                    #print("cards_left",cards_left)
                    #print("total_cards_left",total_cards_left)
                    #print("opp_m",opp_m)
                    hyper_geom=1.0-(math.comb(total_cards_left-cards_left,opp_m)/math.comb(total_cards_left,opp_m)  if total_cards_left >= opp_m and total_cards_left - cards_left >= opp_m else 0.0)
                    ex+=score*hyper_geom #ochekuvane vred e klk se vrednuva
                elif value==2 and math.modf(known_s[2])[0]!=0.5: #ako e dvojka detelina vo igra
                    hyper_geom=1.0-(math.comb(total_cards_left-1,opp_m)/math.comb(total_cards_left,opp_m) if total_cards_left >= opp_m and total_cards_left - 1 >= opp_m else 0.0)
                    ex += (score+1) *hyper_geom #ako zema so nea, se znaa edna e samo
                elif value==10 and math.modf(known_s[10])[0]!=0.5:
                    hyper_geom = 1.0 - (math.comb(total_cards_left - 1, opp_m) / math.comb(total_cards_left, opp_m) if total_cards_left >= opp_m and total_cards_left - 1 >= opp_m else 0.0)
                    ex+= (score+1) *hyper_geom
                #print("Adding, ",hyper_geom)
                hyper+=hyper_geom
        else: #posledna raka od taa runda e
            if last_taken_s==turn:
                if len(taken_s[0])>26-len(table_s):
                    points[0]+=3                    #ako ja prava razlikta od karti da se i ne se uf nego
                for card in table_s:
                    if card[0] in dict_values:
                        points[0]+=dict_values[card[0]]

            else:
                if len(taken_s[1])>26-len(table_s):
                    points[1]+=3
                for card in table_s:
                    if card[0] in dict_values:
                        points[1]+=dict_values[card[0]]
        #da se srede i vrednuvane na zimane karta
        #ako e red na taj so None u rakta, togaj odzimame, else dodavam
        #treba segde taa logika
        me = getattr(self, "hero", 0)
        opp = me ^ 1
        if turn==me:
            EX= points[me] + (len(taken_s[me]) - len(taken_s[opp])) / 52 - points[opp] - ex
        else:
            EX = points[me] + (len(taken_s[me]) - len(taken_s[opp])) / 52 - points[opp] + ex

        #if points[0] == points[1]:
           #print(EX, ex,hyper, points)
        return EX

        #sega treba da se razgledat verojatnostite, na known_s da nadgradame so imame u rakta, 4-known_s, so dvata zaebani sluchaja / , /suma known_s mby so ceilings da se srede
    def current_player(self, state: Any) -> int:
        """+1 for MAX, -1 for MIN. (If you do Expectimax-with-random-opponent,
        you can still set -1, we’ll ignore it if using stochastic-opponent mode.)"""
        return +1
    def legal_moves(self, state: Any) -> Iterable[Any]:
        #tuple of (carta frlena, [karti zemani,koj deluva<--ne za tva]
        moves=[]
        turn=state[1]
        hand=state[0][turn]
        table_s=state[3]
        combinations=generate_possible(table_s) #od tabla sho mozhe da se zema
        for card in hand: #

            all_possible=possible_takes(combinations[card[1]]) #se so mozhe da se zema taka
            if(card[1]==1):
                all_possible.extend(possible_takes(combinations[11])) #dodani Aces u legal moves
            for possible in all_possible:
                moves.append((card,tuple(possible),turn))
        # for move in moves:
        #     print(move)
        return tuple(moves)


    def apply_move(self, state: Any, move: Any) -> Any:
    # state=((players cards), turn,(deck),(table cards), (known),(taken),(br_pisma))
        card,cards_to_take,turn=move
        if(cards_to_take==None):
            print("Cards to take retatrd",move)
        players_s=copy.deepcopy(state[0])
        players_s=list(players_s)
        players_s[turn ^ 1]=[None for val in players_s[turn ^ 1]] #na taj so nee turn ejvaa klk me biva u pichko materino
        taken_s = list(copy.deepcopy(state[5])) #so imat zemano do sega
        pisma = list(state[6])
        table_s = list(state[3])
        known_s = list(copy.deepcopy(state[4]))
        last_taken=state[7]
        phase=state[8] #"chance" "deter"

        new_table=tuple([carda for carda in table_s if carda not in cards_to_take])
        if len(new_table)==0:
            pisma[turn]+=1
        players_s[turn]=[carda for carda in players_s[turn] if carda!=card] #ima maka treba celo players da e tuple
        players_s=tuple(players_s)
        if len(cards_to_take)>0:
            taken_s[turn]=list(taken_s[turn])
            taken_s[turn].extend(list(cards_to_take))
            taken_s[turn].append(card)
        #    taken_s[turn]=tuple(taken_s[turn]) TODO: neka e touple od listi, ak prava problem ke sredame poantatak
        else:
            new_table=list(new_table)
            new_table.append(card)
            new_table=tuple(new_table)

        if card[0] == "2 detelina" or card[0] == "10 baklava":
            known_s[card[1]] += 0.5  # site so gi znaat,
        else:
            known_s[card[1]] += 1

        new_turn=turn ^ 1
        new_last_taken=last_taken
        if len(cards_to_take)>0:
            new_last_taken=turn


        phase="chance"
        #print("apply_move",players_s)
        new_state=(players_s,new_turn,state[2],new_table,tuple(known_s),tuple(taken_s),tuple(pisma),new_last_taken,phase)
        return new_state
        #posle move imame smenano table, player u hand so ima, so imat taken, i known, ushte turn da se smene i sluchaj na pismo
    def has_chance(self, state: Any) -> bool:
        """Return True if the next transition is random (draw, roll, etc.).""" #ako na taj so e red ne gi znaame
        try:
            phase = state[8]
            turn = state[1]
            hand = state[0][turn]
            return phase == "chance"
        except Exception:
            return False
    def chance_outcomes(self, state: Any) -> Iterable[Tuple[float, Any]]:
        """Return all (probability, next_state) from this random event.
        Probabilities must sum to 1."""
        # state=([players cards], turn,[deck],[table cards],[known],[taken],[br_pisma],last_taken,phase) phase e za da znam koga e redno random koga ne [] e touple
        #tuka sreduva phase da e "deter"
        #ke razgledam samo zimane otii preterano
        #print("Chance outcoems called")
        players_s=list(state[0]) #ne ti treba mislam
        table_s=list(state[3])
        known_s=list(state[4])
        taken_s=copy.deepcopy(state[5])
        turn=state[1]
        last_taken_s=state[7]
        pisma_s=list(state[6])
        deck_s=list(state[2])
        combinations=generate_possible(table_s)
        outcomes=[]
        prob=0
        #losh kod ama
        for value in combinations:
            total_cards_left = 52 - sum(math.ceil(x) for x in known_s)  # klk ostanuvat vkupno, neprijatelo klk ima u rakta
            cur_m = len(players_s[turn])
            cards_left = 4 - math.ceil(known_s[value])  # verojatnosta e 0
            if cards_left > 0.5:
                p = 1.0 - (math.comb(total_cards_left - cards_left, cur_m) / math.comb(total_cards_left,cur_m) if total_cards_left >= cur_m and total_cards_left - cards_left >= cur_m else 0.0)
                prob +=p
        for value in combinations:
            #verojatnost da ja ima taa karta u rakta
            total_cards_left=52-sum(math.ceil(x) for x in known_s) #klk ostanuvat vkupno, neprijatelo klk ima u rakta
            cur_m=len(players_s[turn])
            cards_left=4-math.ceil(known_s[value]) #verojatnosta e 0
            sum_probs=0
            if cards_left>0.5: #u elso p==0, mosh i da nema potreba do dusha

                p=1.0-(math.comb(total_cards_left-cards_left,cur_m)/math.comb(total_cards_left,cur_m)  if total_cards_left >= cur_m and total_cards_left - cards_left >= cur_m else 0.0) #hyper geom
                sum_probs +=p
                possiblilities=possible_takes(combinations[value]) #so mozhe da zema, ako
                #print("possibiliteis",possiblilities,"for value ",value,"for combinations ",combinations[value]) #lista od listi
                for possible in possiblilities: #ako zema tva primer so ke se dese, t.e. so table, knwon, taken, br_pisma, last_taken, phase i turn sekak se menat, i deck si ostanva isto
                    to_remove = set(possible) #Chatgpt vika za brzina
                    new_table = [c for c in table_s if c not in to_remove]
                    new_pisma_s=list(pisma_s)
                    if len(new_table) ==0 and len(deck_s)!=0:
                        new_pisma_s[turn]+=1
                    new_taken=copy.deepcopy(taken_s)
                    new_taken[turn].extend(possible) #na taj so moo red, u takeno, dodadi possible so e taj
                    if value==11:
                        card = next(((name, val) for (name, val) in deck_s if val == 1), None) #primer za kartata so bi ja frlil, radi consistency
                    else:
                        card = next(((name, val) for (name, val) in deck_s if val == value), None) #primer za kartata so bi ja frlil, radi consistency

                    if card==None:
                        want = 1 if value == 11 else value
                        face = {12: "J", 13: "Q", 14: "K"}.get(want, str(want))

                        # suits already seen for this rank (ignore None)
                        used = {c[0].split()[1]
                                for pile in (players_s[turn], table_s, *taken_s)
                                for c in pile if c and c[1] == want}

                        suit = next((s for s in ("list", "detelina", "srce", "baklava") if s not in used), None)
                        if suit is None:
                            # No suit of this rank remains -> outcome impossible; skip it
                            continue
                        card = (f"{face} {suit}", want)
                        #card = (f"{face} {suit}", want) if suit else None
                        #print("Was looking for value",value,"got None, known_s for that value is ",known_s[value]) #
                    new_known_s=copy.deepcopy(known_s)
                    if value==11:
                        new_known_s[1]+=1 #oti frle takva karta i saa ja znaame
                    else:
                        new_known_s[value] += 1
                    if len(possible)>0:
                        new_taken[turn].append(card)
                        last_taken_s=turn
                    else:
                        new_table.append(card)
                    new_players_s = list(copy.deepcopy(players_s))
                    if len(players_s[turn])>0:
                       #players_s[turn].pop() #mu se skratuva dolzhiinta za 1, za idni matematiki
                        new_players_s[turn].pop()
                    new_turn=turn^1
                    phase="deter"
                    # state=([players cards], turn,[deck],[table cards],[known],[taken],[br_pisma],last_taken,phase) phase e za da znam koga e redno random koga ne [] e touple
                    #print("cahnce outcomes ",new_players_s)
                    new_state=(tuple(new_players_s),new_turn,tuple(deck_s),tuple(new_table),tuple(new_known_s),tuple(new_taken),tuple(new_pisma_s),last_taken_s,phase)
                    #print(f"{(p/prob)/len(possiblilities)} for value {value}, and for combo {possible} sumprobs {sum_probs/len(possiblilities)}")
                    outcomes.append(((p/prob)/len(possiblilities),new_state))
        return tuple(outcomes)



        # fuck super dlgo pak, znachi presmetuvash verojatnost, gledash kombinacii, so mozhe da zima, t.e. najdobro od combinations, i.e. ili site mozhni, mozhe i site mozhni realno
        # mozhe da zema bilo koo od bilo koite ili da frle, i ako zema od table vadame tva so e zemal, zaedno so eden primer od kartata so frlil


# ---- Node classes ----
NodeType = Literal["MAX", "MIN", "CHANCE"]

@dataclass
class Node:
    state: Any
    depth: int
    node_type: NodeType
    move: Optional[Any] = None          # move taken to reach this node (None at root)
    value: Optional[float] = None       # cached eval
    children: List[Node] = None         # filled on expand
    def __post_init__(self):
        if self.children is None:
            self.children = []

@dataclass
class MaxNode(Node):
    node_type: NodeType = "MAX"

@dataclass
class MinNode(Node):
    node_type: NodeType = "MIN"

@dataclass
class ChanceNode(Node):
    node_type: NodeType = "CHANCE"
def make_node(game: Game, state: Any, depth: int, stochastic_opponent: bool) -> Node:
    if game.has_chance(state):
        return ChanceNode(state, depth)
    p = game.current_player(state)
    if p == +1:   # MAX to move
        return MaxNode(state, depth)
    else:         # MIN to move
        # If you want pure Expectimax where the opponent is random too,
        # you could model opponent as CHANCE instead of MIN:
        return ChanceNode(state, depth) if stochastic_opponent else MinNode(state, depth)


def expand(game: Game, node: Node, stochastic_opponent: bool) -> List[Node]:
    """Generate children for MAX/MIN by legal moves; for CHANCE by chance outcomes."""
    if isinstance(node, ChanceNode):
        node.children = [
            make_node(game, s2, node.depth - 1, stochastic_opponent)
            for (prob, s2) in game.chance_outcomes(node.state)
        ]
        # Store the probabilities on the child nodes (lightweight way):
        for child, (prob, _) in zip(node.children, game.chance_outcomes(node.state)):
            setattr(child, "_prob", prob)
        return node.children

    # MAX or MIN – expand with legal moves
    kids = []
    for mv in game.legal_moves(node.state):
        s2 = game.apply_move(node.state, mv)
        child = make_node(game, s2, node.depth - 1, stochastic_opponent)
        child.move = mv
        kids.append(child)
    node.children = kids
    return kids


def expecti_search(game: Game,
                   root_state: Any,
                   depth: int,
                   stochastic_opponent: bool = False,
                   transpo: Optional[Dict[Any, float]] = None) -> Tuple[float, Optional[Any]]:
    """
    ExpectiMiniMax with optional stochastic opponent:
      - If stochastic_opponent=False: MAX vs MIN with CHANCE nodes
      - If stochastic_opponent=True: MAX vs CHANCE (opponent treated as random)
    Returns (value, best_move) at the root.
    """
    if transpo is None:
        transpo = {}

    def eval_node(node: Node) -> float:
        key = None
        try:
            key = (node.depth, node.node_type, hash_state(node.state))
            if key in transpo:
                node.value = transpo[key]  # <<< set it
                return node.value
        except Exception:
            key = None

        if node.depth == 0 or game.is_terminal(node.state):
            val = game.utility(node.state)
            if key is not None: transpo[key] = val
            node.value = val  # <<< set it
            return val

        children = expand(game, node, stochastic_opponent)
        if isinstance(node, MaxNode):
            val = max(eval_node(c) for c in children) if children else game.utility(node.state)
        elif isinstance(node, MinNode):
            val = min(eval_node(c) for c in children) if children else game.utility(node.state)
        else:
            if not children:
                val = game.utility(node.state)
            else:
                vals = [eval_node(c) for c in children]
                probs = [getattr(c, "_prob", 1.0 / len(children)) for c in children]
                val = sum(p * v for p, v in zip(probs, vals))

        if key is not None: transpo[key] = val
        node.value = val  # <<< set it
        return val



    def hash_state(s: Any) -> int:
        """Make your state hashable; adjust to your state type (tuple, dataclass, str...)."""
        if isinstance(s, (tuple, str, int, float)):
            return hash(s)
        # Example fallback: convert to tuple recursively if dict/list-like
        if isinstance(s, dict):
            return hash(tuple(sorted((k, hash_state(v)) for k, v in s.items())))
        if isinstance(s, (list, set)):
            return hash(tuple(map(hash_state, s)))
        # last resort
        return hash(str(s))

    root = make_node(game, root_state, depth, stochastic_opponent)
    _ = eval_node(root)

    # Pick best move from root if it's a decision node
    if isinstance(root, ChanceNode) or not root.children:
        return (root.value if root.value is not None else game.utility(root_state), None)

    if isinstance(root, MaxNode):
        best = max(root.children, key=lambda c: c.value)
    else:  # MinNode
        best = min(root.children, key=lambda c: c.value)

    return best.value, best.move
def explain_root(game, root_state, depth, stochastic_opponent=False):
    # Build root & expand its children once
    root = make_node(game, root_state, depth, stochastic_opponent)
    kids = expand(game, root, stochastic_opponent)

    # Local cached eval so we don't rebuild another tree for every child
    transpo = {}

    def eval_node(node: Node) -> float:
        key = (node.depth, node.node_type, str(node.state))
        if key in transpo:
            return transpo[key]
        if node.depth == 0 or game.is_terminal(node.state):
            v = game.utility(node.state)
            transpo[key] = v
            node.value = v
            return v
        ch = expand(game, node, stochastic_opponent)
        if isinstance(node, MaxNode):
            v = max(eval_node(c) for c in ch) if ch else game.utility(node.state)
        elif isinstance(node, MinNode):
            v = min(eval_node(c) for c in ch) if ch else game.utility(node.state)
        else:
            if not ch:
                v = game.utility(node.state)
            else:
                vals = [eval_node(c) for c in ch]
                probs = [getattr(c, "_prob", 1.0 / len(ch)) for c in ch]
                v = sum(p * v for p, v in zip(probs, vals))
        transpo[key] = v
        node.value = v
        return v

    scored = []
    for c in kids:
        v = eval_node(c)
        scored.append((v, c.move, type(c).__name__, getattr(c, "_prob", None)))

    scored.sort(key=lambda x: x[0], reverse=True)

    def fmt_move(mv):
        if mv is None: return "None"
        card, take, who = mv
        return f"throw {card} ; take {[x[0] for x in take]} ; by p{who}"

    print("---- root options ----")
    for v, mv, nt, p in scored:
        if p is None:
            print(f"{v: .3f}  {fmt_move(mv)}  node={nt}")
        else:
            print(f"{v: .3f}  {fmt_move(mv)}  node={nt}  p={p: .3f}")
    print("----------------------")

    if kids:
        best = max(scored, key=lambda x: x[0])
        print("BEST:", best[0], fmt_move(best[1]))

dict_values = {
    # Aces
    "1 list": 1, "1 detelina": 1, "1 srce": 1, "1 baklava": 1,

    # Tens (special case for 10 baklava)
    "10 list": 1, "10 detelina": 1, "10 srce": 1, "10 baklava": 2,

    # Jacks
    "J list": 1, "J detelina": 1, "J srce": 1, "J baklava": 1,

    # Queens
    "Q list": 1, "Q detelina": 1, "Q srce": 1, "Q baklava": 1,

    # Kings
    "K list": 1, "K detelina": 1, "K srce": 1, "K baklava": 1,

    # Extra scoring card
    "2 detelina": 1,
}
def score_combo(combo):
    # combo like: [('5 baklava', 5), ('J srce', 12), ...]
    return sum(dict_values.get(name, dict_values.get(name[:2], 0))
               for name, _ in combo)+len(combo)/52
last_taken=0

deck=[]
players=[] #samo so ima u rakata
known=[0]*15
#print(known)
deal_first=0
table=[]
game_points=[]
taken=[[],[]] #tuka so imat zemano, ke sredash dole u taa so trebashe
#print(players)

def print_state():
    for i in range(len(players)):
        print("player",i,":",players[i])
    print("table",table)
    print(game_points)
    print("known",known)
def new_round():
    #known da go isprazne
    global taken,known,table,deck,game_points,deal_first
    deal_first=deal_first^1 #na drugio prvo se dele
    taken[0].clear()
    taken[1].clear()
    table.clear()
    deck=[]
    known.clear() #<-so znaame ima minano, mozhe da napraam len=15, i po edna #TODO mani go tva
    known=[0]*15
    nta={
        "J":12,
        "Q":13,
        "K":14
    }
    for value in ("1","2","3","4","5","6","7","8","9","10","J","Q","K"):
        for sign in ["list","detelina","srce","baklava"]:
            card=list()
            card.append(value+" "+sign)
            if value in nta:
                card.append(nta[value])
            else:
                card.append(int(value))
            ##print(card)
            card=tuple(card)
            deck.append(card)
    random.shuffle(deck)
    cut=random.randint(2, 51)
    #print(deck[cut][1])
    if(deck[cut][0]=="2 detelina" or deck[cut][0]=="10 baklava"):
        known[deck[cut][1]]+=0.5 #opshto known, i posle ka ke razgleduvam da dodadam so ima uf rakata
    else:
        known[deck[cut][1]] += 1
    ##print("deck before cut",deck)
    deck = deck[cut:] + deck[:cut]
    for _ in range(4):
        card=deck.pop()
        if card[0]=="2 detelina" or card[0]=="10 baklava":
            known[card[1]]+=0.5 #site so gi znaat,
        else:
            known[card[1]]+=1
        table.append(card)
    #print_state()
   # #print("new round players,deck,known,table", players, deck, known, table)
def deal_cards(index): #na koj treba prv
    n=len(players)
    for i in range(index,2*n+index):
        print("dealing first to ",index)
        for _ in range(3):
            players[i%n].append(deck.pop())
   # #print("dealing cards, players",players)


def count_points(taken):
    global dict_values,table
    points=[0,0]
    #TODO mosh treba if lem(deck)==0
    if len(taken[0])>26:
        points[0]+=3
    elif len(taken[1])>26:
        points[1]+=3



    for i in range(2):
        for card in taken[i]:
            if card==None:
                print("cards none",taken[i])
            if card[0] in dict_values:
                points[i]+=dict_values[card[0]]
            elif card[0][:2] in dict_values:
                points[i]+=dict_values[card[0][:2]]
    return points

def play_best_move(index):
    #da se generire za poolto site mozhni, pa da sporede svojte vrednosti dal gi ima u dikt, i najvrednoto, a ak nema tam kee int logikta nadezhno, u dikt nekak daa vrednost i indeksi na table,funk generate_possible
    global table,game_points,taken,last_taken
    #move e format turn, card, taken ili neshto taka
    global players, deck, table, known, taken, game_points, last_taken
    # player_to_send=copy.deepcopy(players)
    # player_to_send[index^1]=[None for value in player_to_send[index^1]]
    # # 1) Build the AI root state from your real globals
    root_state = (
        [list(h) for h in players],  # players' hands
        index,  # whose turn in the AI sim
        list(deck),  # deck
        list(table),  # table
        list(known),  # known counts
        [list(p) for p in taken],  # taken piles (team 0/1)
        [0, 0],  # pisma (use 0/0 here; your engine still uses game_points)
        last_taken,  # last_taken team
        "act",  # phase
    )

    # 2) Concrete game instance (inherits the methods you wrote on Game)
    class _G(Game):
        pass

    game = _G()
    game.hero=index

    # 3) Search for the best move (tune depth as you like)
   # explain_root(game, root_state, depth=2, stochastic_opponent=True)
    value, best_move = expecti_search(
        game=game,
        root_state=root_state,
        depth=3,  # try 2–3; higher = slower
        stochastic_opponent=True,
        transpo={}
    )
    #print(best_move)
    thrown=best_move[0]
    to_take=best_move[1]

    #players,table,taken,pismo, last taken,known
    print("player",index,"throws",thrown,"to_take",to_take)
    if len(to_take)>0: #ako zemal carta
        players[index]=[card for card in players[index] if card!=thrown] #frle karta
        taken[index].extend(to_take) #TODO check za touple
        taken[index].append(thrown)
        last_taken=index
        table=[val for val in table if val not in to_take]
        if (len(table)==0) and (len(deck)>0):
            game_points[index]+=1
    else:
        players[index] = [card for card in players[index] if card != thrown]
        table.append(thrown)
    if thrown[0] == "10 baklava" or thrown[0] == "2 detelina":
        known[thrown[1]] += 0.5
    else:
        known[thrown[1]] += 1
    print(table)
def play_hand():
    print(players)
    print(table)
    for i in range(deal_first^1,deal_first^1+len(players)*6):
        play_best_move(i%len(players))

    #print_state()
def play_round():

    while len(deck)>0: #nez klk e razumno tuka da stavam poslednite karti
        deal_cards(deal_first)
        play_hand()
    print("round played, turn when ended",deal_first)
    taken[last_taken].extend(table) #posledni karti da odat nama
    table.clear()
    points=count_points(taken)
    game_points[0]+=points[0]
    game_points[1]+=points[1]
def startgame(num_players): #start za goelmio game
    global game_points
    global players
    if num_players==2:
        players=[[],[]]
    else:
        players=[[],[],[],[]]
    game_points=[0,0]

    while(max(game_points)<101):
        new_round()
        play_round()
        print(game_points)



startgame(2)