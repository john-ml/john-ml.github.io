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
j = s[i + len(left_marker) :].find(right_marker)
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

# If a doc comment ends on [[
#   a multiline 
#   coq code block]]
# And there is no text following it, the extra <div class="paragraph">
# inserted after it produces an annoying amount of space before the next code block.

# Collect a version of the document with no such divs in corrected_text.
corrected_text = ''
while True:
    # Find next possible extra div
    cursed_html = '''<div class="paragraph"> </div>

</span>'''
    i = s.find(cursed_html)
    if i == -1:
        corrected_text += s
        break
    # Check if there's any non-whitespace chars between the cursed html and closing tag of
    # the div holding the doc comment. If there aren't any, remove the extra div.
    j = i + len(cursed_html)
    k = s[j:].find('</div>')
    if s[j : j + k].strip() == '':
        corrected_text += s[:i]
        s = s[i + len(cursed_html.split('\n')[0]) :]
    else:
        corrected_text += s[: j + k]
        s = s[j + k :]
s = corrected_text

with open(sys.argv[1], 'w') as f:
    f.write(s)
