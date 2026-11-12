import sys
from collections import Counter
cnt=Counter(); shown=0
for f in sys.argv[1:]:
  for line in open(f):
    a=line.split('res:')[1].split(); tm=a[-1]; vals=a[:-1]
    if not vals[-1].lstrip('H').isdigit() and vals[-1]!='H': tm=a[-1]; vals=a[:-2]
    vals=[v for v in vals if v=='H' or v.isdigit()]
    hp=''.join('H' if v=='H' else '.' for v in vals)
    if 'H' not in hp: cnt['no halt']+=1; continue
    m=next((m for m in range(2,7) if all(hp[i]==hp[i+m] for i in range(len(hp)-m))),None)
    if m is None: cnt['halt pattern unclear']+=1; continue
    mixing=False; grow=False
    for c in range(m):
        v=[int(x) for i,x in enumerate(vals) if (i+3)%m==c and x!='H']
        if len(v)>=3 and v[-1]>2.5*v[-3]:
            grow=True
            if len({x%m for x in v[1:]})>1: mixing=True
    if not grow: cnt['halts, no growth']+=1; continue
    cnt[('mixing' if mixing else 'collapse',m)]+=1
    if mixing and shown<40: shown+=1; print('MIX mod',m,tm,' '.join(vals))
print(cnt)
