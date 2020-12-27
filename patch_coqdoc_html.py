import sys

with open(sys.argv[1]) as f:
    s = f.read()

# Fix the title: dedent it and make the title of the webpage the same as the title of the article

left_marker = '''<div class="doc">
<a name="lab1"></a><h1 class="section">'''
right_marker = '''</h1>

</div>'''
i = s.find(left_marker)
assert i != -1
j = s[i + len(left_marker):].find(right_marker)
assert j != -1
title = s[i + len(left_marker) : i + len(left_marker) + j]

s = s.replace(left_marker + title + right_marker, f'<h1 class="section">{title}</h1>', 1)
s = s.replace('<title></title>', f'<title>{title}</title>', 1)

# Remove divs that creates horizaontal line/extra space at top of page

s = s.replace('''

<div id="header">
</div>''', '', 1)

s = s.replace('''

<div class="code">

<br/>
</div>''', '', 1)

with open(sys.argv[1], 'w') as f:
    f.write(s)
