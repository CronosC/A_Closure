path = "many.txt"

def clean(str):
    #str = str[:str.rfind("#")]
    str = str.lower()
    str = str.replace("eq", "=")
    str = str.replace("bi", ">")
    str = str.replace("b", "<")
    return str

with open(path) as f:
    qcsps = f.readlines()
    n = 1
    while len(qcsps) > 0:
        q = qcsps[:qcsps.index(".\n")]
        q[0] = "7" + q[0][1:]
        with open(str(n) + ".csp", "w") as o:
            for line in q:
                o.write(clean(line))
        qcsps =  qcsps[qcsps.index(".\n")+1:]
        n = n+1