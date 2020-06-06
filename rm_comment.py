def rm_comment(src):
    comment_level = 0
    i, n = 0, len(src)
    res = []
    while i < n:
        if src[i: i+2] == '(*':
            comment_level += 1
            i += 2
        elif src[i: i + 2] == '*)':
            comment_level -= 1
            i += 2
        else:
            if comment_level == 0:
                res.append(src[i])
            i += 1
    return ''.join(res)

def rm_duplicate_newline(src: str):
    import re
    res = []
    prev_is_empty = True
    nl = re.compile(r'\r?\n')
    for line in nl.split(src):
        if line:
            res.append(line)
            prev_is_empty = False
        elif not prev_is_empty:
            res.append(line)
            prev_is_empty = True
    return '\n'.join(res)


if __name__ == __name__:
    import sys
    fp = sys.argv[1]
    src = open(fp).read()
    src = rm_comment(src)
    src = rm_duplicate_newline(src)
    open(fp, 'w').write(src)