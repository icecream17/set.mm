#!/usr/bin/env python3
"""Build and verify a one-substitution-hypothesis version of eu6w."""
import re
from pathlib import Path
import subprocess
import sys

s=Path("set.mm").read_text()
start=s.index("eu6w $p ")
proof_end=s.index("$.",s.index("$=",start))+2
block_end=s.index("$}",proof_end)+2
prefix=re.sub(r"\$\([\s\S]*?\$\)"," ",s[:start])
floats={}
for m in re.finditer(r"(\S+)\s+\$f\s+(\S+)\s+(\S+)\s+\$\.",prefix):
    label,typ,var=m.groups()
    floats[var]=(label,typ,m.start())

def V(name):
    return ("v",name)
def B(a,b):
    return ("bi",a,b)
def E(a,b):
    return ("eq",a,b)
def Sb(new,old,formula):
    return ("sb",new,old,formula)
X,Y,Z=V("x"),V("y"),V("z")
PH,PS=V("ph"),V("ps")
def emit_ast(t):
    if t[0]=="v":
        assert t[1] in floats,t
        return [floats[t[1]][0]]
    op=t[0]
    if op=="eq":
        return emit_rule("weq",{"x":t[1],"y":t[2]},[])
    if op=="bi":
        return emit_rule("wb",{"ph":t[1],"ps":t[2]},[])
    if op=="sb":
        return emit_rule("wsb",{"x":t[2],"y":t[1],"ph":t[3]},[])
    raise ValueError(t)
def emit_rule(label, substitutions, premises):
    args=sorted(substitutions, key=lambda k:floats[k][2])
    r=[]
    for a in args:
        r+=emit_ast(substitutions[a])
    for p in premises:
        r+=p
    r.append(label)
    return r

h=["eu6w1.h"]
h0=emit_rule("equcoms",{"x":X,"y":Y,"ph":B(PH,PS)},[h])
h1=emit_rule("bicomd",{"ph":E(Y,X),"ps":PH,"ch":PS},[h0])
h2=emit_rule("sbievw",{"x":Y,"y":X,"ph":PS,"ps":PH},[h1])
h3=emit_rule("bicomi",{"ph":Sb(X,Y,PS),"ps":PH},[h2])
h4=emit_rule("a1i",{"ph":B(PH,Sb(X,Y,PS)),"ps":E(X,Z)},[h3])
h5=emit_rule("sbequ",{"x":X,"y":Z,"z":Y,"ph":PS},[])
h6=emit_rule("bitrd",{"ph":E(X,Z),"ps":PH,"ch":Sb(X,Y,PS),"th":Sb(Z,Y,PS)},[h4,h5])
h7=emit_rule("eu6w",{"x":X,"y":Y,"z":Z,"ph":PH,"ps":Sb(Z,Y,PS),"ch":PS},[h6,h])

snippet = """  $""" + "{" + """
    $d x y z $.
    $d ph y z $.
    $d ps x $.
    eu6w1.h $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A one-substitution-hypothesis version of eu6w.
       The second substitution hypothesis is constructed by proper
       substitution and an equality lemma.  (AI proof experiment.) $)
    eu6w1 $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      """+" ".join(h7)+""" $.
  $} 
"""
print("FLOATS", {k:v for k,v in floats.items() if k in ("ph","ps","ch","th","x","y","z")},flush=True)
print("PROOF_LENGTH",len(h7),flush=True)
print("CANDIDATE_START\n",snippet[:4000],flush=True)
saved=Path("proofs/eu6w1.mm").read_text()
assert "eu6w1.h $e" in saved, "checked-in proof missing its hypothesis"
snippet=saved
Path("/tmp/eu6w1_candidate.mm").write_text(snippet)
source=s[:block_end]+"\n"+snippet+"\n"+s[block_end:]
Path("eu6w1_database.mm").write_text(source)
exe=sys.argv[1] if len(sys.argv)>1 else "/home/runner/bin/metamath"
cmd=[exe,"read eu6w1_database.mm","verify proof eu6w1","show trace_back eu6w1 /axioms","exit"]
res=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=150)
print("VERIFIER_OUTPUT\n"+res.stdout[-13000:],flush=True)
bad=("?" in res.stdout or "error(s) were found" in res.stdout.lower() or "not verified" in res.stdout.lower() or "ax-10" in res.stdout or "ax-12" in res.stdout)
assert "MM> verify proof eu6w1" in res.stdout
assert "MM> show trace_back eu6w1 /axioms" in res.stdout
if bad: sys.exit(1)
print("PASS: verifier reported no errors for eu6w1")
