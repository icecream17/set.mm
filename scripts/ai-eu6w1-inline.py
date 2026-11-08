#!/usr/bin/env python3
"""Inline eu6w's existing proof, replacing both substitution hypotheses
with derivations from the single eu6w1.h hypothesis."""
import runpy
import re
import subprocess
import textwrap
from pathlib import Path

env=runpy.run_path("scripts/ai-eu6w1.py")
s=env["s"]
start=s.index("eu6w $p ")
end=s.index("$.",s.index("$=",start))+2
original=s[start:end]
m=re.search(r"\$=\s*\(\s*([^)]*?)\s*\)\s*([A-Z\s]+)\$\.",original)
assert m, original[:500]
extra=m.group(1).split()
proof_body="".join(m.group(2).split())
assert set(proof_body)<set("ABCDEFGHIJKLMNOPQRSTUVWXYZ")

# Parse only declarations and theorem arities before eu6w.
prefix=re.sub(r"\$\([\s\S]*?\$\)"," ",s[:start])
t=re.findall(r"\S+",prefix)
varset=set()
floats=[]
ess=[]
scope=[]
arity={}
i=0
while i<len(t):
    a=t[i]
    if a=="$"+"{":
        scope.append((floats[:],ess[:]))
        i+=1
        continue
    if a=="$}":
        floats,ess=scope.pop()
        i+=1
        continue
    if a in ("$v","$c","$d"):
        j=t.index("$.",i+1)
        if a=="$v":
            varset.update(t[i+1:j])
        i=j+1
        continue
    if a=="$[":
        i=t.index("$]",i+1)+1
        continue
    if i+1<len(t) and t[i+1] in ("$f","$e","$a","$p"):
        label,kind=a,t[i+1]
        j=i+2
        while t[j] not in ("$.","$="):
            j+=1
        expr=t[i+2:j]
        if kind=="$f":
            floats.append((label,expr[1]))
            arity[label]=0
        elif kind=="$e":
            ess.append((label,expr))
            arity[label]=0
        else:
            needed=set(x for x in expr if x in varset)
            for _,e in ess:
                needed.update(x for x in e if x in varset)
            arity[label]=sum(var in needed for _,var in floats)+len(ess)
        if kind=="$p":
            assert t[j]=="$=", (label,t[j])
            j=t.index("$.",j+1)
        i=j+1
        continue
    i+=1

mandatory=["wph","wps","wch","vx","vy","vz","eu6w.x","eu6w.y"]
references=mandatory+extra
print("ORIGINAL_EU6W_LABELS",len(extra),"CODE_CHARS",len(proof_body),flush=True)
print("PARSED_REFERENCE_ARITIES",[(x,arity.get(x)) for x in references[:35]],flush=True)

stack=[]
saved=[]
prefixn=0
for ch in proof_body:
    v=ord(ch)
    if 85<=v<=89:
        prefixn=prefixn*5+v-84
    elif 65<=v<=84:
        index=prefixn*20+v-64-1
        prefixn=0
        if index<len(references):
            label=references[index]
            assert label in arity or label in mandatory,(label,index)
            n=arity.get(label,0)
            if n:
                assert len(stack)>=n,(label,n,len(stack))
                parts=stack[-n:]
                del stack[-n:]
                fragment=[item for part in parts for item in part]+[label]
            else:
                fragment=[label]
            stack.append(fragment)
        else:
            which=index-len(references)
            assert 0<=which<len(saved),(index,which,len(saved))
            stack.append(saved[which][:])
    elif ch=="Z":
        assert stack
        saved.append(stack[-1][:])
assert len(stack)==1, len(stack)
expanded=stack[0]
print("EXPANDED_STEPS",len(expanded),"SAVED_PROOFS",len(saved),flush=True)

X,Y,Z=env["X"],env["Y"],env["Z"]
PH,PS=env["PH"],env["PS"]
Sb=env["Sb"]
mapping={
  "wph":env["emit_ast"](PH),
  "wps":env["emit_ast"](Sb(Z,Y,PS)),
  "wch":env["emit_ast"](PS),
  "vx":env["emit_ast"](X),
  "vy":env["emit_ast"](Y),
  "vz":env["emit_ast"](Z),
  "eu6w.x":env["h6"],
  "eu6w.y":env["h"],
}
full=[piece for label in expanded for piece in mapping.get(label,[label])]
assert "eu6w" not in full
print("INDEPENDENT_STEPS",len(full),flush=True)
text=textwrap.fill(" ".join(full),width=79,initial_indent="      ",subsequent_indent="      ")
snippet="""  $"""+"{"+"""
    $d x y z $.
    $d ph y z $.
    $d ps x $.
    eu6w1.h $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( One-hypothesis form of eu6w, with a proof independent of eu6w. $)
    eu6w1 $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
"""+text+"""
      $.
  $}
"""
print("INDEPENDENT_PROOF_SNIPPET_START\n"+snippet+"\nINDEPENDENT_PROOF_SNIPPET_END",flush=True)
Path("eu6w1_inline_database.mm").write_text(s[:s.rfind("$"+"{",0,start)]+snippet+"\n"+s[s.rfind("$"+"{",0,start):])
exe="/home/runner/bin/metamath"
r=subprocess.run([exe,"read eu6w1_inline_database.mm","verify proof eu6w1","show trace_back eu6w1 /axioms","exit"],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
print("INDEPENDENT_VERIFICATION\n"+r.stdout[-10000:],flush=True)
assert "MM> verify proof eu6w1" in r.stdout
assert "MM> show trace_back eu6w1 /axioms" in r.stdout
assert "?" not in r.stdout and "ax-10" not in r.stdout and "ax-12" not in r.stdout
print("VERIFIED_INDEPENDENT_EU6W1",flush=True)
