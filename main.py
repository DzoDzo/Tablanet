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
import random
from collections import defaultdict

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
first_hand=True
deck=[]
players=[] #samo so ima u rakata
known=[0]*15
print(known)
table=[]
game_points=[]
taken=[[],[]] #tuka so imat zemano, ke sredash dole u taa so trebashe
print(players)
def get_bit(n, k):        return (n >> k) & 1 #pomoshna za kombinations
def set_bit_indices(n: int): #brza nachin za naogjanje na bitvoi so 1 vrednost
    idxs = []
    while n:
        lsb = n & -n                  # isolate lowest 1-bit
        idxs.append(lsb.bit_length() - 1)
        n ^= lsb                      # clear that bit
    return idxs
def print_state():
    for i in range(len(players)):
        print("player",i,":",players[i])
    print("table",table)
    print(game_points)
    print("known",known)
def new_round():
    #known da go isprazne
    global first_hand,taken,known,table
    taken[0].clear()
    taken[1].clear()
    first_hand=True
    global known,deck
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
            #print(card)
            card=tuple(card)
            deck.append(card)
    random.shuffle(deck)
    cut=random.randint(2, 51)
    print(deck[cut][1])
    if(deck[cut][0]=="2 detelina" or deck[cut][0]=="10 baklava"):
        known[deck[cut][1]]+=0.5 #opshto known, i posle ka ke razgleduvam da dodadam so ima uf rakata
    else:
        known[deck[cut][1]] += 1
    #print("deck before cut",deck)
    deck=deck[:cut]+deck[cut:]
    for _ in range(4):
        card=deck.pop()
        if card[0]=="2 detelina" or card[0]=="10 baklava":
            known[card[1]]+=0.5 #site so gi znaat,
        else:
            known[card[1]]+=1
        table.append(card)
    print_state()
   # print("new round players,deck,known,table", players, deck, known, table)
def deal_cards():
    n=len(players)
    for i in range(2*n):
        for _ in range(3):
            players[i%n].append(deck.pop())
   # print("dealing cards, players",players)
def generate_possible(cards):
    #ako gi sortiram, worst case , 1 2 3 4 5 6 7 8 9 10 12 13 14, male i kec treba kak 11 i 1 da se glede, 3 fors idea utre piti chat gpt
    #dict{value:indexi na karti}
    n=len(cards)
    z=0 #tuka ke zapishuvam koi od takvoto se probani
    MASK=(1<<n)-1 #& so tva i dobivam baran broj vrednosti, isto taka od 0 do so ke odame
    combinations = defaultdict(list)
    #za so kec, izbirash situacija dek so eden od nih e 11 samo ednash i posle redovno, i posle dvete sumi gi razgleduvash, Ba si mamata kak ke debagiram ama aj, chatgpt da ti srede raka kak od gornite
    for i in range(int(MASK)):
        z+=1
        ids=set_bit_indices(z)
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
            combinations[suma].append(ids) #ak e validno dodava vrednost so tii sumi tamka
        if first_ace==True and sumA<15:
            combinations[sumA].append(ids)
    return combinations

def count_points():
    global dict_values,table,game_points,taken

    if len(taken[0])>len(taken[1]):
        game_points[0]+=3
    elif len(taken[1])>len(taken[0]):
        game_points[1]+=3

    for i in range(2):
        for card in taken[i]:
            if card[0] in dict_values:
                game_points[i]+=dict_values[card[0]]
            elif card[0][:2] in dict_values:
                game_points[i]+=dict_values[card[0][:2]]
    print_state()

def play_best_move(index):
    #da se generire za poolto site mozhni, pa da sporede svojte vrednosti dal gi ima u dikt, i najvrednoto, a ak nema tam kee int logikta nadezhno, u dikt nekak daa vrednost i indeksi na table,funk generate_possible
    global table,game_points,taken,last_taken
    choices=generate_possible(table)
    print(choices)
    for i in range(len(players[index])):
        print(players[index][i],choices)
        if players[index][i][1] in choices: #tuka ke treba pododbra logika,
            #treba karta da ode u taken index%2, ama i od table da ode kurban
            card=players[index].pop(i)
            #treba da popname listata od index, i posle for indexes in list od table pop do dek so treba
            #tuka treba logikata za kak najnogo se uprauva, prvo ednostavnoto, so da frle da spase glava, posle so da frle da e najsafe, t.e. so kombinacija najretko ili najnevredni karti
            idxs = sorted(set(choices[card[1]][0]))  #indexi na karti so ke se zemat od masa zgolemuvajki
            to_take = [table[i] for i in idxs] #tii so ke gi zemame
            table = [x for j, x in enumerate(table) if j not in set(idxs)] #table od ka ke otstraname zemani
            if card[0] == "2 detelina" or card[0] == "10 baklava":
                known[card[1]] += 0.5  # site so gi znaat,
            else:
                known[card[1]] += 1 #so ja frle taj ja otkriva, 0.5 oznachuva specialni akrti kak 2 detelina i 10 baklava
            taken[index % 2].extend(to_take)
            taken[index%2].append(card)
            last_taken=index%2

            print("Player threw card",card,"taking",to_take)

            if len(table)==0 and first_hand==False:
                game_points[index%2]+=1
                print(f"Pismo! Za ekipa {index%2}")
            print_state()
            return
    table.append(players[index].pop())
    print_state()

def play_hand():
    global first_hand
    for i in range(len(players)*6):
        play_best_move(i%len(players))
        first_hand=False
    print_state()
def play_round():
    while len(deck)>0: #nez klk e razumno tuka da stavam poslednite karti
        deal_cards()
        play_hand()
    taken[last_taken].extend(table) #posledni karti da odat nama
    count_points()
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



startgame(4)
