from subprocess import Popen, PIPE

def run_sat_solver(asdf='asdf.cnf'):
    p = Popen(['./picosat', asdf], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    output, err = p.communicate(b"input data that is passed to subprocess' stdin")
    rc = p.returncode
    return output


def decode(sat_encoding):
    lines = sat_encoding.split("\n")
    res = {}
    for l in lines[1:]:
        info_arr = l[2:].split(" ")
        for var_str in info_arr:
            var_num = int(var_str)
            if var_num == 0:
                return res
            if var_num > 0:
                res[var_num] = True
            if var_num < 0:
                res[abs(var_num)] = False

sat_output = run_sat_solver(asdf='easy1.cnf')
print decode(sat_output)
