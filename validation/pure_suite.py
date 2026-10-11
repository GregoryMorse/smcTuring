"""Finite native validation scenarios plus independent TM observations."""
import random
import struct
from pathlib import Path
from generate_pure import CELLS

def address(n): return (1, n)
def offset(b): return (0, int(b))
def zigzag(n): return 2*n if n >= 0 else -2*n-1

def tm_case(name, alphabet, states, transitions, input_symbols, blank=0, limit=1000, steps=None):
    table_limit = alphabet+1+5*alphabet*states
    def cell(p): return table_limit+zigzag(p)
    rows = {q: sorted((a, *result) for (state, a), result in transitions.items() if state == q) for q in range(states)}
    def node(q, i=0): return alphabet+1+5*(i+alphabet*q)
    def head(q): return node(q) if rows[q] else 0
    registers = [offset(False) for _ in range(13)]
    registers[1] = offset(True)
    registers[2:7] = [address(head(0)), address(cell(0)), address(cell(-1)), address(cell(1)), address(0)]
    memory = {}
    for q, entries in rows.items():
        for index, (trigger, symbol, direction, destination) in enumerate(entries):
            start = node(q, index)
            words = [address(start+1), address(node(q, index+1) if index+1<len(entries) else 0),
                     address(trigger+1), address(start+2), address(symbol+1), address(start+3),
                     offset(direction), address(start+4), address(head(destination)), offset(False)]
            for k, value in enumerate(words): memory[2*start+k] = value
    for index in range(table_limit, CELLS):
        encoded = index-table_limit
        p = encoded//2 if encoded%2 == 0 else -(encoded//2)-1
        memory[2*index] = address((input_symbols[p] if 0 <= p < len(input_symbols) else blank)+1)
        next_cell = cell(p-1 if p < 0 else p+1)
        # The native test has a finite initialized interior; it never reaches
        # the boundary. No assertion of fixed-width unboundedness is made.
        memory[2*index+1] = address(next_cell) if next_cell<CELLS else offset(False)
    tape = {p:s for p,s in enumerate(input_symbols)}
    state = position = count = 0
    while steps is None or count < steps:
        symbol = tape.get(position, blank)
        result = transitions.get((state, symbol))
        if result is None: break
        symbol, direction, state = result
        tape[position] = symbol
        position += 1 if direction else -1
        count += 1
        assert count <= 10000, name
    halted = transitions.get((state, tape.get(position, blank))) is None
    if steps is not None: assert not halted, name
    expected = {2*cell(p):address(tape.get(p,blank)+1) for p in range(-32,129)}
    assert max(expected)<2*CELLS
    return {"name":name,"limit":limit,"fault":halted,"head":cell(position),"registers":registers,
            "memory":memory,"expected":expected,"tm_steps":count}

def cases():
    result = [tm_case("empty-table",2,1,{},[1]),
              tm_case("one-right-step",2,2,{(0,0):(1,True,1)},[]),
              tm_case("one-left-step",2,2,{(0,0):(1,False,1)},[]),
              tm_case("nonmatching-then-match",2,2,{(0,0):(0,False,1),(0,1):(0,True,1)},[1]),
              tm_case("missing-trigger",2,1,{(0,0):(1,True,0)},[1]),
              tm_case("left-right-outside-input",3,4,{(0,0):(1,False,1),(1,0):(2,True,2),(2,1):(2,True,3)},[]),
              tm_case("right-walk-prefix",2,1,{(0,0):(1,True,0),(0,1):(1,True,0)},[],limit=48,steps=48),
              tm_case("left-walk-prefix",2,1,{(0,0):(1,False,0),(0,1):(1,False,0)},[],limit=48,steps=48)]
    # Original repository addition table, including its undefined state 2.
    raw = [(1,'0','0','R',1),(1,'1','1','R',1),(1,'_','_','R',3),
           (3,'0','0','R',3),(3,'1','1','R',4),(3,'_','_','R',2),
           (4,'0','0','R',4),(4,'1','1','R',4),(4,'_','_','L',5),
           (5,'0','1','L',5),(5,'1','0','L',6),(6,'0','0','L',6),
           (6,'1','1','L',6),(6,'_','_','L',7),(7,'1','0','L',7),
           (7,'0','1','R',1),(7,'_','1','R',1)]
    symbols = {'0':0,'1':1,'_':2}
    transition = {(q-1,symbols[a]):(symbols[b],d=='R',r-1) for q,a,b,d,r in raw}
    result.append(tm_case("original-addition-0100_1001_",3,7,transition,[symbols[a] for a in "0100_1001_"],blank=2))
    addition = result[-1]
    addition_base = 3+1+5*3*7
    addition_output = ''.join("01_"[addition["expected"][2*(addition_base+zigzag(p))][1]-1] for p in range(10))
    assert addition_output == "1101_0000_", addition_output
    addition["expected_output"] = addition_output
    for direction, name in [(True,"closed-right-walk-48"),(False,"closed-left-walk-48")]:
        transitions = {(q,0):(1,direction,q+1) for q in range(48)}
        result.append(tm_case(name,2,49,transitions,[]))
    # Poison the source offset register to exercise the new explicit tag guard.
    for tag in [False, True]:
        case = {"name":"invalid-offset" if tag else "invalid-base","limit":1,"fault":True,"head":0xffffffff,
                "registers":[offset(False) for _ in range(13)],"memory":{},"expected":{}}
        case["registers"][1] = offset(True)
        case["registers"][6] = address(0)
        case["registers"][2] = address(1) if tag else offset(False)
        if tag: case["registers"][0] = address(2)
        result.append(case)
    rng = random.Random(0x534d43)
    # These are source MOV states, including heavy aliasing and arbitrary
    # address/offset tags. Their expected result is the separate MOV interpreter.
    for index in range(96):
        def random_word(): return address(rng.randrange(16)) if rng.randrange(3) else offset(rng.randrange(2))
        registers = [random_word() for _ in range(13)]
        registers[0],registers[1],registers[6] = offset(False),offset(True),address(0)
        registers[2] = address(rng.randrange(1,16))
        memory = {p:random_word() for p in range(32)}
        result.append({"name":f"alias-tags-{index}","limit":1,"fault":None,"head":0xffffffff,
                       "registers":registers,"memory":memory,"expected":{}})
    return result

def reference_fault(case, instructions):
    registers = list(case["registers"])
    memory = dict(case["memory"])
    for op,a,b,c in instructions:
        a = int(a)
        if op == "imm": registers[a] = offset(int(c)); continue
        base, off = (int(b),int(c)) if op=="load" else (a,int(b))
        address_word, offset_word = registers[base],registers[off]
        if address_word[0] != 1 or offset_word[0] != 0: return True
        p = 2*address_word[1]+offset_word[1]
        if op=="load": registers[a] = memory.get(p,offset(False))
        else: memory[p] = registers[int(c)]
    return False

def write_suite(path: Path, instructions):
    suite = cases()
    with path.open("wb") as out:
        def number(n): out.write(struct.pack("<I",int(n)))
        def word(w): number(w[0]); number(w[1])
        out.write(b"SMC1"); number(len(suite))
        for case in suite:
            if case["fault"] is None: case["fault"] = reference_fault(case, instructions)
            name = case["name"].encode()
            number(len(name)); out.write(name)
            number(case["limit"]);number(case["fault"]);number(case["head"])
            for w in case["registers"]: word(w)
            number(len(case["memory"]))
            for p,w in case["memory"].items(): number(p);word(w)
            number(len(case["expected"]))
            for p,w in case["expected"].items(): number(p);word(w)
    return [{k:v for k,v in case.items() if k in ["name","limit","fault","head","tm_steps","expected_output"]} for case in suite]
