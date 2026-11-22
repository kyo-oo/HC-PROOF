import re
path = '/home/z/hc-repo/GSTFiniteLinePointAlgebra.lean'
with open(path, 'rb') as f:
    data = f.read().decode('utf-8')

# The corruption deleted "[" plus the first character of the first token
# of many "rw [...]" commands.  Repair by explicit rules.
fixes = [
    ('rw ]', 'rw [h]'),
    ('rw round,', 'rw [hround,'),
    ("rw t',", "rw [ht',"),
    ('rw Pzero,', 'rw [hPzero,'),
    ('rw ke]', 'rw [hke]'),
    ('rw top]', 'rw [htop]'),
    ('rw a, hcon]', 'rw [ha, hcon]'),
    ('rw e0,', 'rw [he0,'),
    ('rw ja]', 'rw [hja]'),
    ('rw mul,', 'rw [hmul,'),
    ('rw zero]', 'rw [hzero]'),
    ('rw bidx]', 'rw [hbidx]'),
    ('rw sum]', 'rw [hsum]'),
    ('rw dm]', 'rw [hdm]'),
    ('rw eq]', 'rw [heq]'),
    ('rw em_lineGenericIdeal_iff M i]', 'rw [mem_lineGenericIdeal_iff M i]'),
    ('rw ap_sub,', 'rw [map_sub,'),
    ('rw em_closedOutsideIdealRingAt,', 'rw [mem_closedOutsideIdealRingAt,'),
    ('rw hgf,', 'rw [hgf,'),
    ('rw hybardef]', 'rw [hybardef]'),
]
total = 0
for old, new in fixes:
    n = data.count(old)
    if n:
        data = data.replace(old, new)
        total += n
        print(f"{n:3d} x  {old!r} -> {new!r}")
with open(path, 'wb') as f:
    f.write(data.encode('utf-8'))
print("TOTAL FIXED:", total)
# report any remaining suspicious sites
rem = [ (i, l.strip()[:110]) for i, l in enumerate(data.split('\n'), 1)
        if re.search(r'\brw\s+[^\[\s]', l) ]
print("REMAINING SUSPECT:", len(rem))
for i, l in rem:
    print(f"{i}: {l}")
