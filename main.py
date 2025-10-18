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
#TODO negde kec i 11 dvete ti gi stava mozni
#Majnuvam son ebago
from __future__ import annotations

import copy
import math
import random
import heapq


SEED = 12345
random.seed(SEED)
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
def table_points(table):
    return sum(dict_values.get(name, dict_values.get(name[:2], 0))
               for (name, _) in table if name)
def p_no_forbidden(m, b, k):
    g = m - b
    if k < 0 or b < 0 or g < 0 or k > m:
        return 0.0
    if k > g:
        return 0.0
    return math.comb(g, k) / math.comb(m, k)
def score_combo(combo):
    # combo like: [('5 baklava', 5), ('J srce', 12), ...]
    #print(combo)
#print("combo",combo)
    suma=0
    sumA=0
    first_ace=True
    add=0
    for card in combo:
        if first_ace and card[1]==1:
            sumA+=10
            first_ace=False
        suma += card[1]
        sumA += card[1]

    if suma in [1,10,11,12,13,14] or sumA in [1,10,11,12,13,14]:
        add=1
    return sum(dict_values.get(name, dict_values.get(name[:2], 0))
               for name, _ in combo)+len(combo)/52+add
def safest_throw(known,hand):
    safest_ns=(None,0)
    safest_ss=(None,0)
    #print("safest throw gets known hnad",known,hand)
    for card in hand:
        if known[card[1]]>=3:
            return card
        if card[0] not in dict_values:
            if math.floor(known[card[1]])>=safest_ns[1]:
                safest_ns=card
        else:

            if math.floor(known[card[1]])>=safest_ss[1]:
                safest_ss=card
    if safest_ns[0] is not None:
        return safest_ns
    return safest_ss

def fabricate_card(value,cards):
    if value==11:
        value=1
    hlp=["srce","list","detelina","baklava"]
    if value==2:
        hlp = ["srce", "list",  "baklava","detelina"]

    seen=set()
    splitted=None
    prevod={
        12:"J " ,
        13:"Q ",
        14:"K "
    }
    card=None
    for card in cards:
        if card[1]==value:
            splitted=card[0].split(" ")
            buja = splitted[1]
            seen.add(buja)
    if splitted is None:
        #print("Zaebal si neshto, ja ti list")
        if value in prevod:
            card=(prevod[value]+"list",value)
        else:
            card=(str(value)+" list",value)
        return card
    for buja in hlp:
        if buja not in seen:
            card=(splitted[0]+" "+buja,value)
            break
    return card
def play_out(me,turn,player_s,known_s,decky,tabley):
    possible_cards=player_s[me^1]+decky
    random.shuffle(possible_cards)
    new_hands=[[],[]]
    new_hands[me]=list(player_s[me])

    point_diff=0
    took_last=-1
    card_diff=0

    for i in range(len(player_s[me^1])):
        new_hands[me ^ 1].append(possible_cards.pop())

        # print("best_moves",best_moves_dict)

    while len(new_hands[me])>0 or len(new_hands[me^1])>0:
        best_moves = most_valuable(generate_possible(tabley))
        topk = heapq.nlargest(14, best_moves.items(),
                              key=lambda kv: score_combo(kv[1]))
        #print("turns tunr",turn,"lenths",len(new_hands[turn]),len(new_hands[turn^1]))
        hero_hand_dict = {num: (string, num) for string, num in new_hands[me]}
        opp_hand_dict = {num: (string, num) for string, num in new_hands[me ^ 1]}
        hands_dicts = [[], []]
        hands_dicts[me] = hero_hand_dict
        hands_dicts[me ^ 1] = opp_hand_dict
        took=False
        for key,value in topk:
            if key in hands_dicts[turn]:
                turns_cards=hands_dicts[turn]
                took = True
                thrown = turns_cards[key]

                to_take = value
                if turn==me:
                    point_diff+=score_combo(to_take)
                    card_diff+=len(to_take)+1
                else:
                    point_diff -= score_combo(to_take)
                    card_diff -= len(to_take) + 1

                took_last = turn
                tabley = [val for val in tabley if val not in to_take]
                if (len(tabley) == 0) and (len(decky) > 0):
                    if turn==me:
                        point_diff+=1
                    else:
                        point_diff-=1
                break
        if took == False:
            most_thrown = -1
            thrown = None
            for card in new_hands[turn]:
                if known_s[card[1]] > most_thrown:
                    thrown = card
                    most_thrown = known_s[card[1]]
            tabley.append(thrown)
        hands_dicts[turn].pop(thrown[1], None)
        #print("thrown",thrown)
        new_hands[turn] = [card for card in new_hands[turn] if card != thrown]  # frle karta
        if thrown[0] == "10 baklava" or thrown[0] == "2 detelina":
            known_s[thrown[1]] += 0.5
        else:
            known_s[thrown[1]] += 1
        turn=turn^1
    return point_diff,card_diff,took_last
    #print("play_out sees the follwoing",point_diff,card_diff,took_last," for player turn ",turn,"hero is ",me)
def evaluate_table(table,top_combos,known_s,lenth_hand): #da issimuliram raci
    if(len(table)==0):
        return -1
    suma=0
    br=0
    num_verboten=0
    total_cards=52-sum(math.ceil(x) for x in known_s)
    for key,value in top_combos:
        #print(f"key is : {key} with cards left {4-math.ceil(known_s[key])}")
        num_verboten+=4-math.ceil(known_s[key])
        if(len(value)==len(table)):
            suma+=1
        suma+=score_combo(value)
        br+=1
    if suma!=0:
        suma/=br
        p=p_no_forbidden(m=total_cards,b=num_verboten,k=lenth_hand) #ver da ne izvleche ni edna od scoring so se
        suma*=(1-p)
    return suma+len(table)*0.25
def simulate_table(most_valuable,hand_lenth,cards_left,sims):
    max_valued_combo=-1
    sum=0

    for i in range(sims):
        simulated_hand = random.sample(cards_left, k=hand_lenth)
        for card in simulated_hand:
            value=card[1]
            if card[1]==1:
                value=11
            if value in most_valuable:
                max_valued_combo=score_combo(most_valuable[value])
        sum+=max_valued_combo
    return sum/sims
def draw_1ormore_with_k_illegal(n, N=52, K=4, Ka=4):
    if N <= 0 or n <= 0 or K <= 0 or n > N:
        return 0.0
    den = math.comb(N, n) if 0 <= n <= N else 0
    if den == 0:
        return 0.0

    # ensure upper arguments for comb are valid
    if N - Ka < n:  # too many cards requested after removing illegal
        return 1.0  # must draw at least one illegal/legal anyway
    if N - Ka - K < n:
        num = 0  # all remaining cards are legal
    else:
        num = math.comb(N - Ka, n) - math.comb(N - Ka - K, n)

    return num / den if den else 0.0
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
    viable_combos.sort(key=score_combo,reverse=True)

    viable_combos.append([])
    #print("viable combos",viable_combos)

    return viable_combos
def most_valuable(combis):
    best={}

    for value in combis:
        best_agregate = []
        combo=combis[value]
        n=len(combo)
        missing = set(range(n))
        max_score=0
        cur_score=0
        while missing:
            agregate = list()
            for i in range(n):
                if not any(x in combo[i] for x in agregate) and i in missing:
                    agregate.extend(combo[i]) #ke vratame lista od
                    missing.discard(i)
            agregate=list(agregate)
            if len(agregate)!=0:
                cur_score=score_combo(agregate)
            if(cur_score > max_score):
                max_score=cur_score
                best_agregate=list(agregate)
        best[value]=list(best_agregate)
    #print(best)
    return best
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
        #tuka da sredam tva so last player, empty deck,malce po preciznost dek najdam

        taken_s=list(state[5])
        pisma=state[6]
        table_s=state[3]
        known_s=copy.deepcopy(state[4])
        known_s=list(known_s)
        deck_s=copy.deepcopy(state[2])
        turn=state[1]
        players_s=copy.deepcopy(state[0])
        last_taken_s=state[7]
        me = getattr(self, "hero", 0)
        opp = me ^ 1

        for card in players_s[me]:  # znaa site so znaat+negovite
            if card is not None:
                if card[0] == "2 detelina" or card[0] == "10 baklava":
                    known_s[card[1]] += 0.5  # site so gi znaat,
                else:
                    known_s[card[1]] += 1


        combinations = generate_possible(table_s)
        best_dict = most_valuable(combinations)
        topk = heapq.nlargest(14, best_dict.items(),
                              key=lambda kv: score_combo(kv[1]))

        points=[0,0]
        if len(players_s[1])==0 and len(players_s[0])==0: #ako dvujcata neamt karti, dodadi ako prazen table taj soo nared -0.5
            if len(deck_s)>0:
                points[turn]+=simulate_table(most_valuable=best_dict,hand_lenth=6,cards_left=deck_s,sims=200) #slednio pat ke ima 6 kartio
            # else:
            #     points[last_taken_s]+=table_points(table_s)
            #     if len(taken_s[last_taken_s])+len(table_s)>26:
            #         points[last_taken_s]+=3
            #     else:
            #         points[last_taken_s^1]+=3

           # print(table_s)
           # print(f"points for both hands empty, for turn {turn} is",points )

        elif len(players_s[opp])==0: #TODO maybeee ushte eden uslov ama ne mee logichno
           # print("here opp==turn^1,",opp==turn^1)
            tmp_table=list()
            to_take=()
            tmp_lt=last_taken_s
            if players_s[me][0][1] in best_dict:        #ako imam so da frlam frli
                tmp_lt=me
                card_val=players_s[me][0][1] if players_s[me][0][1] != 1 else 11
                to_take=best_dict[card_val]
                #print(f" the card {players_s[turn][0]} is in {best_dict} taking {to_take}")
                points[me]+=score_combo(to_take)
                tmp_table=[card for card in table_s if card not in to_take]
                if len(tmp_table)==0 and len(deck_s)>0:
                    points[me]+=1
            else:
                tmp_table=list(table_s)
                tmp_table.append(players_s[me][0])
               # print("Table after throwing players card ",tmp_table)
            if len(deck_s)>0:
                if len(to_take)>0: #ako zemal turn neshto, na nov table gledame najarno
                    tmp_combinations = generate_possible(tmp_table) #bavno ama da go ebam saa :D
                    tmp_best_dict = most_valuable(tmp_combinations)
                    tmp_topk = heapq.nlargest(14, tmp_best_dict.items(), key=lambda kv: score_combo(kv[1])) #novata sostojba na table
                    points[opp]+=simulate_table(most_valuable=best_dict,hand_lenth=6,cards_left=deck_s,sims=200) #povtorno ke ima site karti dushmano
            else:
                #print(tmp_table)
                points[tmp_lt]+=table_points(tmp_table)
                add=len(to_take)
                # if len(taken_s[tmp_lt])+len(tmp_table)+add+1>26:
                #     points[tmp_lt]+=3
                # else:
                #     points[tmp_lt^1]+=3
           # print("opponents hand emtpy")
        elif len(players_s[me])==0: #jas nemam dushmano ima edna,ver da zema mosh treba u sluchaj dek==0, ono mozhame da proverame dali negovata karta zima nesh
            if len(deck_s)>0:
                points[opp]+=simulate_table(most_valuable=best_dict,hand_lenth=6,cards_left=list(deck_s)+list(players_s[opp]),sims=200)
            else:
                if players_s[opp][0][1] in best_dict: #ako mozhe da zema, zima, pa broome dali ima pokje
                    if players_s[opp][0][1] in dict_values:
                        points[opp]+=table_points(table_s)+dict_values[players_s[opp][0][0]]
                    else:
                        points[opp] += table_points(table_s)
                # if len(taken_s[opp]) + len(table_s) + 1> 26:
                #     points[opp] += 3
                # else:
                #     points[opp ^ 1] += 3
        else: #od 1card va 1card nagore
            to_take = ()
            tmp_table=list(table_s)
            if turn==me:
                for key,value in topk:
                    for card in players_s[me]:
                        if card[1]==key:
                            to_take = value
                            points[me]+=score_combo(to_take)
                            tmp_table=[card for card in table_s if card not in to_take]
                            break
                if len(to_take)==len(table_s)!=0 and len(deck_s)+len(players_s[turn^1])>0:
                    points[me]+=1
                # if len(to_take)+len(taken_s[me])+1>26:
                #     points[me]+=3
                if len(to_take)==0:
                    #nogo slozhena e profi safest throw, odame onaka
                    throw_card=safest_throw(known_s,players_s[me]) #mozhe karta da vrakje
                    tmp_table=[card for card in table_s]
                    tmp_table.append(throw_card)

                tmp_combinations = generate_possible(tmp_table)  # bavno ama da go ebam saa :D
                tmp_best_dict = most_valuable(tmp_combinations)
                tmp_topk = heapq.nlargest(14, tmp_best_dict.items(), key=lambda kv: score_combo(kv[1]))
                points[opp]+=evaluate_table(tmp_table,tmp_topk,known_s,len(players_s[opp]))
            else:
                points[opp]+=evaluate_table(tmp_table,topk,known_s,len(players_s[opp]))
        points[0] += pisma[0]
        points[1] += pisma[1]
        points[me]+=table_points(taken_s[me])
        points[opp]+=table_points(taken_s[opp])

        R = len(deck_s) + len(table_s) + len(players_s[0]) + len(players_s[1])
        D = len(taken_s[me]) - len(taken_s[opp])
        majority_ev = 3.0 * math.tanh(D / max(1.0, math.sqrt(R)))

        return points[me]-points[opp]+majority_ev

        #dvujcata si imat kart, taj na red da napraa move, pa drugio da
        # tested_point_diff=0
        # tested_card_diff=0
        # tested_took_last=0
        #
        #
        # sims=20
        # for i in range(sims):
        #     tpd,tcd,ttl=play_out(me, turn, list(players_s), list(known_s), list(deck_s), list(table_s))
        #     tested_point_diff+=tpd
        #     tested_card_diff+=tcd
        #     if ttl==1:
        #         tested_took_last+=1
        #     if ttl==0:
        #         tested_took_last-=1
        # tested_point_diff=tested_point_diff/sims
        # tested_card_diff=tested_card_diff/sims
        # #print("tested point diff",tested_point_diff)
        # #print("tested card diff",tested_card_diff)
        #
        # if tested_took_last>0:
        #     tested_took_last=1
        # else:
        #     tested_took_last=0
        #
        #
        #
        # #print(taken_s)

        # if (len(deck_s) < 1):
        #     points[tested_took_last] += 1


        # #tuka da imam funkcija so naogje najvredni kombinacii
        # #print(table_s)


        if len(players_s[turn^1])==0 and len(players_s[turn])==0: #ako drgio ima karti, oa ima igra
            print("Evaluating  position with no card in hands")
        points = count_points(taken_s)
        points[0] += pisma[0]
        points[1] += pisma[1]


        print(topk)
        evt=evaluate_table(table_s,topk,known_s,len(players_s[turn]))
        print(f"Evaluated table {evt} \n",table_s)
        #print("topk",topk)
        ex=0

        opp_m = len(players_s[opp])  #drugio klk karti ima u rakta
        #if  math.modf(known_s[2])[0]==0.5:
        total_cards_left = 52-sum(math.ceil(x) for x in known_s) #kolku karti imat pominato

        not_takeable=0
        can_take=False

        sum_ex=0
        prob=0
        if len(deck_s) > 0 or len(players_s[turn]) > 0:
            scoring_combos = 0
            for key, combo in topk:
                if len(combo) > 0:
                    scoring_combos += 1
                cards_left = 4 - math.ceil(known_s[key])  # verojatnosta e 0
                not_takeable += cards_left
                if cards_left > 0.5:
                    p = 1.0 - (math.comb(total_cards_left - cards_left, opp_m) / math.comb(total_cards_left,
                                                                                           opp_m) if total_cards_left >= opp_m and total_cards_left - cards_left >= opp_m else 0.0)
                    prob += p
                    value = score_combo(combo)
                    sum_ex=max(sum_ex,value*p)
            # print("peak sum_ex",sum_ex)
            # ochekuvana vrednost za protivnik. dole treba da ja odzemame
            if total_cards_left - not_takeable > 0:
                # print("when zero",table_s,players_s,total_cards_left,opp_m)
                p_none = math.comb(total_cards_left - not_takeable, opp_m) / math.comb(total_cards_left, opp_m)
            elif opp_m == 0:
                p_none = 1
            else:
                p_none = 0
            ex = 0
            value_to_combo = dict(topk)
            for card in players_s[me]:
                if card[1] in value_to_combo:
                    # print("Adding points of max combo to my turn, ",me,turn)
                    can_take = True
                    if card[1] == 1:
                        ex += score_combo(value_to_combo[11])
                    elif card[0] == "2 detelina" or card[0] == "10 baklava":
                        ex += score_combo(value_to_combo[card[1]]) + 1  # tva e ofcourse pozitivno, ama ak ne flexe tuak
                    else:
                        ex += score_combo(value_to_combo[card[1]])
                    break
            #prob += p_none
            #if sum_ex != 0:
                #sum_ex = sum_ex / prob  # faktichki go norm do negde
            if turn==me:
                #print("Entered utility for my turn")
                #print("Entered utility for my turn")
                ex=0
                value_to_combo = dict(topk)
                for card in players_s[turn]:
                    if card[1] in value_to_combo:
                        #print("Adding points of max combo to my turn, ",me,turn)
                        if card[1]==1:
                            ex += score_combo(value_to_combo[11])
                        elif card[0]=="2 detelina" or card[0]=="10 baklava":
                            ex += score_combo(value_to_combo[card[1]])+1 #tva e ofcourse pozitivno, ama ak ne flexe tuak
                        else:
                            ex += score_combo(value_to_combo[card[1]])
                        if len(value_to_combo[card[1]])==len(table_s):
                            points[me]+=1
                        print("Its my turn Ex is ",ex)
                        break
                    ex=-sum_ex
            else:
                sum_ex = sum_ex - p_none * ex

                #shansa da nema nishto e kjar na moo strana, blago hevristichki, oti e nogo poarno za mene
        else:#evaluatenuvame krajna pozicija ako nema vekje karti u raktta
            for card in table_s+tuple(players_s[turn^1]):
                if card[0] in dict_values:
                    points[last_taken_s] += dict_values[card[0]]
                if len(table_s)+len(players_s[last_taken_s]) > 26 > len(players_s[last_taken_s]) and len(players_s[last_taken_s^1])<26:
                    points[last_taken_s] +=3
        card_weight=0
        weight = 0
        if len(players_s[turn^1]) <26 and len(players_s[turn])<26:
            card_weight=(len(players_s[me])-len(players_s[opp]))*0.1
        else:
            if last_taken_s==me:
                weight=2
            else:
                weight=-2
        #points[tested_took_last]+=2

       # if turn==me: #i obratno treba da proba
            #print("Utility calculated on my turn")
        #points[tested_took_last]+=10/(52-len(players_s[me]+players_s[me^1])-len(deck_s)) #klk karti ima u igra,
        EX= (points[me] - points[opp])+(len(taken_s[me])-len(taken_s[opp]))*4/52 #card weight e polosho za seed bar, utre ke istestirame

        return EX
      #  else:
            #print("sum_ex",sum_ex)
           # EX = points[me] -  points[opp]+tested_point_diff
            #print("Utility calculated on opp turn")


        # if turn!=me: #i obratno treba da proba
        #     print("can_take")
        #     EX= points[me] - points[opp] + ex e tva nekak raboteu pichko materino, so 115 107
        #
        # else:
        #     EX = points[me] +  points[opp] - sum_ex



        # num_restircted=0
        # for card_val in takeable:
        #     num_restircted+=math.ceil(known_s[card_val])
        #
        #
        #
        #
        #
        #
        # if len(deck_s) > 0 or len(players_s[turn]) > 0: #
        #     for key,value in topk:
        #         cards_left = 4 - math.ceil(known_s[1]) if key in (1, 11) else 4 - math.ceil(known_s[key])
        #         if key==11:
        #             cards_left =4- math.ceil(known_s[1])
        #         if not_takeable==0:
        #             p = 1.0 - (math.comb(total_cards_left - cards_left, opp_m) / math.comb(total_cards_left,opp_m) if total_cards_left >= opp_m and total_cards_left - cards_left >= opp_m else 0.0)
        #         else:
        #             p=draw_1ormore_with_k_illegal(n=opp_m, N=total_cards_left,Ka=not_takeable,K=cards_left)
        #         score = score_combo(value) #klk skor dobiva
        #         if key==2:   #licnite da se sredat
        #             if math.modf(known_s[2])[0]!=0.5:
        #                 score+=1
        #         if key==10:
        #             if math.modf(known_s[10])[0]!=0.5:
        #                 score+=1
        #
        #         if (len(value) == len(table_s)!=0):
        #             score += 1
        #         #print(f"prob for {key}: {p}, not_takeable {not_takeable}")
        #         not_takeable += cards_left
        #         ex += score * p
        #     if (
        #             opp_m <= 0
        #             or total_cards_left <= 0
        #             or opp_m > total_cards_left
        #             or total_cards_left - not_takeable <= 0
        #             or opp_m > total_cards_left - not_takeable
        #     ):
        #         p_none = 0.0
        #     else:
        #         p_none = math.comb(total_cards_left - not_takeable, opp_m) / math.comb(total_cards_left, opp_m)
        #     if turn==me:
        #         #print("Entered utility for my turn")
        #         ex=0
        #         value_to_combo = dict(topk)
        #         for card in players_s[turn]:
        #             if card[1] in value_to_combo:
        #                 #print("Adding points of max combo to my turn, ",me,turn)
        #                 can_take=True
        #                 if card[1]==1:
        #                     ex += score_combo(value_to_combo[11])
        #                 elif card[0]=="2 detelina" or card[0]=="10 baklava":
        #                     ex += score_combo(value_to_combo[card[1]])+1 #tva e ofcourse pozitivno, ama ak ne flexe tuak
        #                 else:
        #                     ex += score_combo(value_to_combo[card[1]])
        #                 break
        # #print("pinon",p_none)
        # else:#evaluatenuvame krajna pozicija ako nema vekje karti u raktta
        #     for card in table_s:
        #         if card[0] in dict_values:
        #             points[last_taken_s] += dict_values[card[0]]
        #         if len(table_s)+len(players_s[last_taken_s]) > 26 > len(players_s[last_taken_s]) and len(players_s[last_taken_s^1])<26:
        #             points[last_taken_s] +=3
        #
        # me = getattr(self, "hero", 0)
        # opp = me ^ 1
        # cards_weight=0
        # if(len(players_s[0]) < 26 or len(players_s[1]) < 26):
        #     cards_weight=(len(taken_s[me]) - len(taken_s[opp])) / (52-total_cards_left) #losha idea (52-total_cards_left)
        # if can_take: #i obratno treba da proba
        #     print("can_take")
        #     EX= points[me] + cards_weight- points[opp] + ex
        #
        # else:
        #     EX = points[me] +  cards_weight - points[opp] - ex



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
            if card[1]==1:
                all_possible=possible_takes(combinations[11]) #se so mozhe da se zema taka
            else:
                all_possible=possible_takes(combinations[card[1]]) #dodani Aces u legal moves
            for possible in all_possible:
                moves.append((card,tuple(possible),turn))
        # for move in moves:
        #     print(move)
        return tuple(moves)


    def apply_move(self, state: Any, move: Any) -> Any:
    # state=((players cards), turn,(deck),(table cards), (known),(taken),(br_pisma))
        card,cards_to_take,turn=move
        #if(cards_to_take==None):
            #prit("Cards to take retatrd",move)
        players_s=copy.deepcopy(state[0])
        players_s=list(players_s)
        #players_s[turn ^ 1]=[None for val in players_s[turn ^ 1]] #na taj so nee turn ejvaa klk me biva u pichko materino
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
    def chance_outcomes(self, state: Any) -> Iterable[Tuple[float, Any]]: #znachi imash chance i se so mozhe da naprava protivniko, dali da odam apsolutno ili nekak poefikasno
        """Return all (probability, next_state) from this random event.
        Probabilities must sum to 1."""
        #maybeeeee, za site non_taking verojatnosti i sostojbi, dek so ver ke im gi normalizirme na p_none, mosh i mozhe direk klk left
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
        #takeable=[]
        total_cards_left = 52 - sum(math.ceil(x) for x in known_s)+len(players_s[turn])  # klk ostanuvat vkupno, neprijatelo klk ima u rakta
        cur_m = len(players_s[turn])

        best_dict = most_valuable(combinations)
        topk = heapq.nlargest(14, best_dict.items(),
                              key=lambda kv: score_combo(kv[1]))
        #best_moves_dict = dict(topk)
        not_takeable=0

        p_none = 0
        taking_cards=[]

        new_players_s = list(copy.deepcopy(players_s))
        if len(players_s[turn]) > 0:
            # players_s[turn].pop() #mu se skratuva dolzhiinta za 1, za idni matematiki
            new_players_s[turn].pop()
        new_turn = turn ^ 1
        phase = "deter"

        for key, value in topk:

            taking_cards.append(key)
            cards_left = 4 - math.ceil(known_s[1]) if key in (1, 11) else 4 - math.ceil(known_s[key])
            if key == 11:
                cards_left = 4 - math.ceil(known_s[1])
            if not_takeable == 0:
                p = 1.0 - (math.comb(total_cards_left - cards_left, cur_m) / math.comb(total_cards_left,
                                                                                       cur_m) if total_cards_left >= cur_m and total_cards_left - cards_left >= cur_m else 0.0)
            else:
                p = draw_1ormore_with_k_illegal(n=cur_m, N=total_cards_left, Ka=not_takeable, K=cards_left)
            prob += p
            to_throw=fabricate_card(key,players_s[turn]+deck_s)
            to_remove = set(value)
            new_known_s=copy.deepcopy(known_s)
            new_taken=copy.deepcopy(taken_s)
            new_table=copy.deepcopy(table_s)

            new_pisma_s = list(pisma_s)

            new_table = [c for c in table_s if c not in to_remove]
            not_takeable += cards_left
            if len(new_table) == 0 and len(deck_s) != 0:
                new_pisma_s[turn] += 1
            if key == 11:
                new_known_s[1] += 1  # oti frle takva karta i saa ja znaame
            elif to_throw[0]=="2 detelina" or to_throw[0]=="10 baklava":
                new_known_s[key] += 0.5
            else:
                new_known_s[key] += 1
            if len(value) > 0:
                new_taken[turn].append(to_throw)
                last_taken_s = turn
            else:
                new_table.append(to_throw)

            new_state = (
            tuple(new_players_s), new_turn, tuple(deck_s), tuple(new_table), tuple(new_known_s), tuple(new_taken),
            tuple(new_pisma_s), last_taken_s, phase)

            outcomes.append((p , new_state))

        p_this=0
        for value in [1,2,3,4,5,6,7,8,9,10,12,13,14]:
            if value not in taking_cards:
                if known_s[value] == 3:
                    to_throw_this=fabricate_card(value,players_s[turn]+deck_s)
                    p_this=draw_1ormore_with_k_illegal(n=cur_m, N=total_cards_left,Ka=not_takeable,K=1)
                to_throw=fabricate_card(value,players_s[turn]+deck_s)

        if p_this >0:
            new_table=copy.deepcopy(table_s)
            new_table.append(to_throw_this)
            new_known_s=copy.deepcopy(known_s)

            if to_throw_this[1] == 11:
                new_known_s[1] += 1  # oti frle takva karta i saa ja znaame
            elif to_throw_this[0] == "2 detelina" or to_throw_this[0] == "10 baklava":
                new_known_s[to_throw_this[1]] += 0.5
            else:
                new_known_s[to_throw_this[1]] += 1

            new_state = (
                tuple(new_players_s), new_turn, tuple(deck_s), tuple(new_table), tuple(new_known_s), tuple(taken_s),
                tuple(pisma_s), last_taken_s, phase)

            outcomes.append((p_this, new_state))

        p_none=1-prob-p_this #prva karta so mozhe da ja zabode
        if p_none > 0:
            new_table = copy.deepcopy(table_s)
            new_table.append(to_throw)
            new_known_s = copy.deepcopy(known_s)

            if to_throw[1] == 11:
                new_known_s[1] += 1  # oti frle takva karta i saa ja znaame
            elif to_throw[0] == "2 detelina" or to_throw[0] == "10 baklava":
                new_known_s[to_throw[1]] += 0.5
            else:
                new_known_s[to_throw[1]] += 1

            new_state = (
                tuple(new_players_s), new_turn, tuple(deck_s), tuple(new_table), tuple(new_known_s), tuple(taken_s),
                tuple(pisma_s), last_taken_s, phase)

            outcomes.append((p_none, new_state))



        # for value in combinations:
        #     takeable.append(value)
        #     cards_left = 4 - math.ceil(known_s[value])  # verojatnosta e 0
        #     if cards_left > 0.5:
        #         p = 1.0 - (math.comb(total_cards_left - cards_left, cur_m) / math.comb(total_cards_left,cur_m) if total_cards_left >= cur_m and total_cards_left - cards_left >= cur_m else 0.0)
        #         prob +=p #p e veojatnsota da ima karta za tva combo
        #     #print(f"for value {value}, prob is {p}")
        # #od takeable da izbroom klk ima,i posle niz dec da najdam nekoo so [1] not in takebla,jako
        # num_restircted=0
        # for card_val in takeable:
        #     num_restircted+=math.ceil(known_s[card_val])
        # #ver da ne izvleche ni edna
        # if total_cards_left-num_restircted>=1: #ako se site restricted taman e "verojatnosta si tere
        #     p_none=math.comb(total_cards_left-num_restircted,cur_m)/math.comb(total_cards_left,cur_m)
        #     if prob==0:
        #         p_none=1
        #     prob+=p_none
        #     thrown_card=None
        #     for card in deck_s+players_s[turn^1]:
        #         if card[1] not in takeable:
        #             thrown_card=card
        #     if thrown_card is None:
        #         print("Function is being used")
        #         for value in [1,2,3,4,5,6,7,8,9,10,11,12,13,14]:
        #             if value not in takeable:
        #                 print("Function is being used inner")
        #                 thrown_card=fabricate_card(value,deck_s+players_s[turn^1])
        #                 print("thrown_card",thrown_card)
        #                 break
        #     if thrown_card is not None:
        #         new_table=copy.deepcopy(table_s)
        #         new_table.append(thrown_card)
        #         new_table=tuple(new_table)
        #         new_players_s=copy.deepcopy(players_s)
        #         new_known_s=copy.deepcopy(known_s)
        #         if thrown_card[0]=="10 baklava" or thrown_card[0]=="2 detelina":
        #             new_known_s[thrown_card[1]]+=0.5
        #         else:
        #             new_known_s[thrown_card[1]]+=1
        #         if len(players_s[turn]) > 0:
        #             # players_s[turn].pop() #mu se skratuva dolzhiinta za 1, za idni matematiki
        #             new_players_s[turn].pop()
        #         new_turn = turn ^ 1
        #         phase = "deter"
        #         new_state = (
        #         tuple(new_players_s), new_turn, tuple(deck_s), tuple(new_table), tuple(new_known_s), tuple(taken_s),
        #         tuple(pisma_s), last_taken_s, phase)
        #         if prob==0:
        #             print(f"Prbo is 0 while pnon and total cards left {total_cards_left} and num_forbiddenis {num_restircted}  ",p_none,players_s,"\n",table_s,"\n",deck_s)
        #         outcomes.append((p_none/prob,new_state))
        # for value in combinations:
        #     val = value
        #     if value == 11:
        #         val = 1
        #     #verojatnost da ja ima taa karta u rakta
        #     total_cards_left=52-sum(math.ceil(x) for x in known_s) #klk ostanuvat vkupno, neprijatelo klk ima u rakta
        #     cur_m=len(players_s[turn])
        #     cards_left=4-math.ceil(known_s[val]) #verojatnosta e 0
        #
        #     if cards_left>0.5: #u elso p==0, mosh i da nema potreba do dusha
        #
        #         p=1.0-(math.comb(total_cards_left-cards_left,cur_m)/math.comb(total_cards_left,cur_m)  if total_cards_left >= cur_m and total_cards_left - cards_left >= cur_m else 0.0) #hyper geom
        #
        #         possible=best_dict[value]  #so mozhe da zema, ako
        #         #possibilities=possible_takes(combinations[value])
        #         #print(f"Moznosti za {value},",possiblilities)
        #         #print("possibiliteis",possiblilities,"for value ",value,"for combinations ",combinations[value]) #lista od listi
        #        # for possible in possiblilities: #ako zema tva primer so ke se dese, t.e. so table, knwon, taken, br_pisma, last_taken, phase i turn sekak se menat, i deck si ostanva isto
        #         to_remove = set(possible) #Chatgpt vika za brzina
        #
        #         new_table = [c for c in table_s if c not in to_remove]
        #         new_pisma_s=list(pisma_s)
        #         if len(new_table) ==0 and len(deck_s)!=0:
        #             new_pisma_s[turn]+=1
        #         new_taken=copy.deepcopy(taken_s)
        #         new_taken[turn].extend(possible) #na taj so moo red, u takeno, dodadi possible so e taj
        #         new_known_s=copy.deepcopy(known_s)
        #
        #         card=fabricate_card(value,deck_s+players_s[turn])
        #         print("card after",card)
        #         if value==11:
        #             new_known_s[1]+=1 #oti frle takva karta i saa ja znaame
        #         else:
        #             new_known_s[value] += 1
        #         if len(possible)>0:
        #             new_taken[turn].append(card)
        #             last_taken_s=turn
        #         else:
        #             new_table.append(card)
        #         new_players_s = list(copy.deepcopy(players_s))
        #         if len(players_s[turn])>0:
        #            #players_s[turn].pop() #mu se skratuva dolzhiinta za 1, za idni matematiki
        #             new_players_s[turn].pop()
        #         new_turn=turn^1
        #         phase="deter"
        #         # state=([players cards], turn,[deck],[table cards],[known],[taken],[br_pisma],last_taken,phase) phase e za da znam koga e redno random koga ne [] e touple
        #         #print("cahnce outcomes ",new_players_s)
        #         new_state=(tuple(new_players_s),new_turn,tuple(deck_s),tuple(new_table),tuple(new_known_s),tuple(new_taken),tuple(new_pisma_s),last_taken_s,phase)
        #         #print(f"{(p/prob)/len(possiblilities)} for value {value}, and for combo {possible} sumprobs {sum_probs/len(possiblilities)}")
        #         outcomes.append(((p/prob),new_state))
        # #print(f"sum_probs={sum(p for p, _ in outcomes):.6f}")
        #if sum(p for p, _ in outcomes)<1:
            #print("Prob for none =0", prob, p_none,p_this,players_s[turn], "\n", table_s, "\n", players_s[turn ^ 1])
        return tuple(outcomes)


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
    # if(deck[cut][0]=="2 detelina" or deck[cut][0]=="10 baklava"): me mrze gore da sreduvam ver
    #     known[deck[cut][1]]+=0.5 #opshto known, i posle ka ke razgleduvam da dodadam so ima uf rakata
    # else:
    #     known[deck[cut][1]] += 1
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
        #print("dealing first to ",index)
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
    thrown=None
    if index==1:
        took=False
        best_moves=most_valuable(generate_possible(table))
        topk = heapq.nlargest(14, best_moves.items(),
                              key=lambda kv: score_combo(kv[1]))
        best_moves_dict=dict(topk)
        #print("best_moves",best_moves_dict)
        for card in players[index]:
            if card[1] in best_moves_dict:
                took=True
                thrown=card

                to_take=best_moves[card[1]]
                taken[index].extend(to_take)  # TODO check za touple
                taken[index].append(thrown)
                last_taken = index
                table = [val for val in table if val not in to_take]
                if (len(table) == 0) and (len(deck) +len(players[0])+len(players[1])> 1):
                    game_points[index] += 1
        print("player ",index," throws", thrown)
        if took==False:
            most_thrown=-1
            thrown=None
            #najdame najretka karta
            for card in players[index]:
                if known[card[1]] > most_thrown:
                    thrown=card
                    most_thrown=known[card[1]]
            table.append(thrown)
        players[index] = [card for card in players[index] if card != thrown]  # frle karta
        print("player ",index," throws", thrown)
        if thrown[0] == "10 baklava" or thrown[0] == "2 detelina":
            known[thrown[1]] += 0.5
        else:
            known[thrown[1]] += 1
        print(table)
    # 2) Concrete game instance (inherits the methods you wrote on Game)
    else:
        class _G(Game):
            pass

        game = _G()
        game.hero=index

        # 3) Search for the best move (tune depth as you like)
        #explain_root(game, root_state, depth=4, stochastic_opponent=True)
        value, best_move = expecti_search(
            game=game,
            root_state=root_state,
            depth=2,  # try 2–3; higher = slower
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
            if (len(table)==0) and (len(deck)+len(players[0])+len(players[1])>0):
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
    #print("round played, turn when ended",deal_first)
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


N = 5  # how many tablanet games to run
p0_wins = p1_wins = ties = 0
startgame(2)
# for g in range(N):
#     # reset globals that can leak across games
#     last_taken = 0
#     players = [[], []]
#     known = [0] * 15
#     deck = []
#     table = []
#     taken = [[], []]
#     game_points = [0, 0]
#
#     # optional: vary RNG per game for diversity
#     #random.seed(SEED + g)
#
#     startgame(2)  # plays until someone reaches 101+
#
#     # winner = player with more points at the final print
#     if game_points[0] > game_points[1]:
#         p0_wins += 1
#     elif game_points[1] > game_points[0]:
#         p1_wins += 1
#     else:
#         ties += 1
#
# print(f"\n=== Summary over {N} games ===")
# print(f"P0 wins: {p0_wins}")
# print(f"P1 wins: {p1_wins}")
# print(f"Ties:    {ties}")