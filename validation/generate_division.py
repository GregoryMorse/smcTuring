"""Emit the printed Listing 12 instruction order with only M06/M11 repairs.

Explicit DWORD types resolve the paper's pseudo-assembly; labels are namespaced
for four separate fixtures. Host setup/observation remain outside pure execution.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def instance(index, mod, sign):
    name = "Div" + str(index)
    lines = [
        name + "Native PROC",
        "push ebx", "push esi", "push edi", "push ebp",
        "mov eax, [esp+20]", "mov edx, [esp+24]",
        "mov [DivObservation+36], esp", "bt edx, 0",
        "mov ebx, 13579bdfh", "mov ecx, 2468ace0h", "mov edx, 0badc0deh",
        "mov esi, 11223344h", "mov edi, 55667788h", "mov ebp, 76543210h",
        name + "PureBegin:",
    ]
    labels = [6,8,9,10,11,12,13,14,15,16,17,18,20,21]
    if sign:
        labels += [0,2,3,4,5,22,23]
        if not mod: labels += [1]
        lines += [
            "mov DWORD PTR [lbl0+6], 80000000h",
            "xchg DWORD PTR [x], eax", "and DWORD PTR [lbl0+6], eax",
            "xchg DWORD PTR [x], eax",
        ]
        if not mod:
            lines += [
                "mov DWORD PTR [lbl1+6], 80000000h",
                "xchg DWORD PTR [y], eax", "and DWORD PTR [lbl1+6], eax",
                "xchg DWORD PTR [y], eax",
                "lbl0: xor DWORD PTR [lbl1+6], 80000000h",
            ]
        selected = "lbl0" if mod else "lbl1"
        lines += [
            "shr DWORD PTR ["+selected+"+6], 31",
            "neg DWORD PTR ["+selected+"+6]",
            selected+": mov DWORD PTR [lbl22+6], 80000000h",
            "xchg DWORD PTR [x], eax",
            "mov DWORD PTR [lbl20+6], eax", "mov DWORD PTR [lbl3+6], eax",
            "shl DWORD PTR [lbl3+6], 1", "xchg DWORD PTR [x], eax",
            "mov DWORD PTR [lbl2+6], 0",
            "sub DWORD PTR [lbl20+6], 80000000h", "sbb DWORD PTR [lbl2+6], 0",
            "add DWORD PTR [lbl20+6], 80000000h", "not DWORD PTR [lbl2+6]",
            "lbl2: and DWORD PTR [lbl3+6], 80000000h",
            "lbl3: sub DWORD PTR [lbl20+6], 80000000h",
            "xchg DWORD PTR [y], eax",
            # M11a: initialize the divisor's own immediate.
            "mov DWORD PTR [lbl13+6], eax", "mov DWORD PTR [lbl5+6], eax",
            "shl DWORD PTR [lbl5+6], 1", "xchg DWORD PTR [y], eax",
            "mov DWORD PTR [lbl4+6], 0",
            "sub DWORD PTR [lbl13+6], 80000000h", "sbb DWORD PTR [lbl4+6], 0",
            "add DWORD PTR [lbl13+6], 80000000h", "not DWORD PTR [lbl4+6]",
            "lbl4: and DWORD PTR [lbl5+6], 80000000h",
            "lbl5: sub DWORD PTR [lbl13+6], 80000000h",
            "xchg DWORD PTR [lbl13+6], eax", "mov DWORD PTR [lbl14+6], eax",
            "xchg DWORD PTR [lbl13+6], eax",
        ]
    else:
        lines += [
            "xchg DWORD PTR [x], eax", "mov DWORD PTR [lbl20+6], eax",
            "xchg DWORD PTR [x], eax", "xchg DWORD PTR [y], eax",
            "mov DWORD PTR [lbl13+6], eax", "mov DWORD PTR [lbl14+6], eax",
            "xchg DWORD PTR [y], eax",
        ]
    def continuation(label):
        return [label+":", "xchg DWORD PTR [stptr+6], esp",
                "add DWORD PTR [stptr+6], 4", "xchg DWORD PTR [stptr+6], eax",
                "mov DWORD PTR [stptr+2], eax", "xchg DWORD PTR [stptr+6], eax"]
    lines += [
        "mov DWORD PTR [lbl21+6], 0",
        "mov DWORD PTR [lbl6+6], 32", # M06c.
        "lbl6: mov DWORD PTR [lbl6+6], 80000000h",
        "xchg DWORD PTR [stptr+6], esp",
        # NEAR code-label typing is intentionally retained.
        "call [lbl7]",
    ]
    lines += continuation("lbl7")
    lines += [
        "mov DWORD PTR [lbl9+6], 0", "neg DWORD PTR [lbl6+6]",
        "sbb DWORD PTR [lbl9+6], 0", "neg DWORD PTR [lbl6+6]",
        "not DWORD PTR [lbl9+6]",
        "mov DWORD PTR [lbl8+6], lbl19-lbl10-1-4", # M11b.
        "lbl8: and DWORD PTR [lbl9+6], 80000000h",
        "lbl9: xor DWORD PTR [lbl10+1], 80000000h",
        "xchg DWORD PTR [stptr+6], esp",
        "lbl10: call [lbl10+1+4]",
    ]
    lines += continuation("lbldivbody") # M11c; existing location only.
    lines += [
        "xchg DWORD PTR [lbl20+6], eax",
        "mov DWORD PTR [lbl11+6], eax", "mov DWORD PTR [lbl12+6], eax",
        "xchg DWORD PTR [lbl20+6], eax",
        "shl DWORD PTR [lbl20+6], 1", "shl DWORD PTR [lbl21+6], 1",
        "mov DWORD PTR [lbl18+6], 1",
        "lbl11: sub DWORD PTR [lbl20+6], 80000000h",
        "adc DWORD PTR [lbl21+6], 0",
        "lbl12: add DWORD PTR [lbl20+6], 80000000h",
        "lbl13: mov DWORD PTR [lbl17+6], 80000000h",
        "mov DWORD PTR [lbl15+6], 0",
        "lbl14: sub DWORD PTR [lbl21+6], 80000000h",
        "sbb DWORD PTR [lbl15+6], 0",
        "lbl15: and DWORD PTR [lbl17+6], 80000000h",
        "xchg DWORD PTR [lbl15+6], eax", "mov DWORD PTR [lbl16+6], eax",
        "xchg DWORD PTR [lbl15+6], eax", "not DWORD PTR [lbl16+6]",
        "lbl16: and DWORD PTR [lbl18+6], 80000000h",
        "lbl17: add DWORD PTR [lbl21+6], 80000000h",
        "lbl18: add DWORD PTR [lbl20+6], 80000000h",
        "dec DWORD PTR [lbl6+6]",
        "xchg DWORD PTR [stptr+6], esp", "call [lbl7]",
    ]
    lines += continuation("lbl19")
    lines += ["mov DWORD PTR [lbl10+1], 0"] # M11d.
    if mod:
        lines += ["lbl20: mov DWORD PTR [lbl20+6], 80000000h",
                  "lbl21: mov DWORD PTR [result], 80000000h"]
    else:
        lines += ["lbl20: mov DWORD PTR [result], 80000000h",
                  "lbl21: mov DWORD PTR [lbl21+6], 80000000h"]
    if sign:
        lines += [
            "xchg DWORD PTR [result], eax",
            "mov DWORD PTR [lbl23+6], eax", "shl DWORD PTR [lbl23+6], 1",
            "xchg DWORD PTR [result], eax",
            "lbl22: and DWORD PTR [lbl23+6], 80000000h",
            "lbl23: sub DWORD PTR [result], 80000000h",
        ]
    lines += [
        name+"PureEnd:",
        "mov [DivObservation+0], eax", "mov [DivObservation+4], esp",
        "mov [DivObservation+8], ebx", "mov [DivObservation+12], ecx",
        "mov [DivObservation+16], edx", "mov [DivObservation+20], esi",
        "mov [DivObservation+24], edi", "mov [DivObservation+28], ebp",
        "pushfd", "pop DWORD PTR [DivObservation+32]",
        "mov esp, [DivObservation+36]", "pop ebp", "pop edi", "pop esi", "pop ebx", "ret",
        name+"Native ENDP",
        name+"X: mov DWORD PTR ["+name+"X+6], 0",
        name+"Y: mov DWORD PTR ["+name+"Y+6], 0",
        name+"Result: mov DWORD PTR ["+name+"Result+6], 0",
    ]
    import re
    def rename(line):
        line=re.sub(r'\blbl(\d+)\b',lambda m:name+"L"+m[1],line)
        line=re.sub(r'\blbldivbody\b',name+"Body",line)
        for token, target in [('x',name+'X+6'),('y',name+'Y+6'),('result',name+'Result+6')]:
            line=re.sub(r'\b'+token+r'\b',target,line)
        return line.replace(':','::')
    code="\n".join(rename(line) for line in lines)+"\n"
    fields=[name+"X+6",name+"Y+6",name+"Result+6",
            name+"L10+1","stptr+6","stptr+2"]
    fields += [name+"L"+str(label)+"+6" for label in labels if label!=10]
    table=name+"Fields DWORD OFFSET "+fields[0]+"\n"
    table+="".join("DWORD OFFSET "+field+"\n" for field in fields[1:])
    table+=name+"Descriptor DWORD OFFSET "+name+"Native, OFFSET "+name+"Fields, "+str(len(fields))+", "+str(int(mod))+", "+str(int(sign))+"\n"
    return code, table

def generate():
    parts=[instance(i,mod,sign) for i,(mod,sign) in enumerate([(False,False),(True,False),(False,True),(True,True)])]
    code=".686\n.model flat, C\noption casemap:none\n.data\nPUBLIC DivObservation\nDivObservation DWORD 10 DUP(0)\n.code\nDivBegin:\n"
    code+="".join(part[0] for part in parts)
    code+="stptr: mov DWORD PTR [stptr+6], OFFSET stptr+6\nDivEnd:\n"
    for name,target in [('GetDivBegin','DivBegin'),('GetDivEnd','DivEnd'),('GetDivTable','DivTable')]:
        code+=name+" PROC\nmov eax, OFFSET "+target+"\nret\n"+name+" ENDP\n"
    for i in range(4):
        code+="PUBLIC Div"+str(i)+"Native\n"
    code+=".const\n"+"".join(part[1] for part in parts)
    code+="DivTable DWORD "+", ".join("OFFSET Div"+str(i)+"Descriptor" for i in range(4))+"\nEND\n"
    return code

if __name__=="__main__":
    target=ROOT/'validation/.build/division/native.asm'
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(generate(),encoding='utf-8')
