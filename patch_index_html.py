import sys

with open(sys.argv[1]) as f:
    s = f.read()

s = s.replace(' [GitHub] [CV]', '', 1)

with open(sys.argv[1], 'w') as f:
    f.write(s)
