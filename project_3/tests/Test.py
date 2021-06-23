"""
Author: Bart Meyers, Brent van Bladel
Date: October 2012

usage: python Test.py --logisimpath=<path> testtype <file_to_compile.txt> <file_to_test.circ>
         testtypes:
             -a     :   test alu
             -s     :   test simple datapath (only r-type and sb/lb)
             -f     :   test full datapath (all instructions)
         --logisimpath=<path>
             sets logisim jar to <path>

Needs to be in the same folder as logisim-generic-2.7.1.jar

This program will convert test cases (currently only ALU tests) to logisim dat files,
which can be loaded into your logisim project. If this project includes the main circuit
of ALU_GroupXX.circ, running this program with the project as last argument will behave
as a test run: logisim will read in a test and oracle, and produce outputs for each test.
Then, this program will parse this output and verify whether the test result is the same
as the oracle.

To support different datapaths, make changes starting from "Variability" label until
"End Variability" label (end of file).
"""

import sys, re, os
from argparse import ArgumentParser
from pprint import pprint

def pattern(patterns, can_have_label=False):
    fullpattern = r'^\s*' # pattern must start in the beginning of a line
    if can_have_label:
        fullpattern += "(?P<label>(%s:\s)?)" % labelpattern()
        fullpattern += r'\s*'
    for key, value in patterns:
        fullpattern += "(?P<%s>%s)" % (key, value) # then, add the patterns
        fullpattern += r'\s+'
    fullpattern += "(?P<comment>(#.*)?)$" # a comment might be added at the end of the line
    return re.compile(fullpattern)
# some conversions
def int2bin(s, width): # convert a signed integer to a two's complement bin notation
    if (int(s) > 2**(int(width)-1)-1 or int(s) < -(2**(int(width)-1))):
        raise ValueError("Number %s exceeds supported range of [%d, %d]" % (s, -(2**(int(width)-1)), 2**(int(width)-1)-1))
    else:
        return bin(int(s))[2:].rjust(int(width), "0") if not s.startswith("-") else bin((2**int(width))+int(s))[2:]
def uint2bin(s, width): # convert a positive integer to a bin notation (can be two's complement or not - same notation)
    if (int(s) > 2**(int(width))-1 or int(s) < 0):
        raise ValueError("Number %s exceeds supported range of [%d, %d]" % (s, 0, 2**(int(width))-1))
    else: # only positive number
        return bin(int(s))[2:].rjust(int(width), "0")
def reg2bin(s, width): # convert a register string to a bin notation (width bits)
    return uint2bin(s.lstrip('r').lstrip('$r'), int(width))
def label2bin(s, width, symboltable, count_from=None): # convert a label to a binary jump value (by looking in the symboltable), if count_from (int) than jump relative to that memory address
    if count_from is None:
        return int2bin(str(symboltable[s]), int(width))
    else:
        return int2bin(str(symboltable[s] - count_from - 1), int(width))
def ubin2hex(s, width): # convert a binary number to a hexadecimal number
    if len(s) != int(width):
        raise ValueError("Binary number %s should be width %d, but is width %d" % (s, int(width), len(s)))
    else:
        return "%x" % int(s, 2)
# some patterns for matching numbers
def integerpattern():
    return r'[+-]?\d+'
def uintegerpattern():
    return r'\+?\d+'
def binarypattern(n):
    return r'[01]{%d}' % n
def register():
    return "r(?:"+"|".join([str(i) for i in range(0, REGISTER_ADDRESS_SIZE**2)])+")"
def writeregister():
    return "r(?:"+"|".join([str(i) for i in set(range(0, REGISTER_ADDRESS_SIZE**2))-set(READONLY_REGISTERS)])+")"
def labelpattern():
    return r'[a-zA-Z_]\w*'

def dec2twoscompl_hex(s, width):
    if s.startswith("-"):
        return "%x" % ((2**int(width))+int(s))
    elif len(s) == width: # in case of a binary string
        return "%x" % int(s, 2)
    else:
        return "%x" % int(s)

def twoscompl_bin2dec(s, width=None):
    s = s.replace(" ", "")
    if not width:
        width = len(s)
    return (int(s, 2)-2**int(width)) if s[0] == '1' else int(s, 2)

def findallfiles(path, pattern, subfolders=True): # find all files in path whose file matches a given pattern
    def match(pattern, f):
        return re.match(pattern, f) and not f.startswith(".")
    goodfiles = []
    if subfolders:
        for r,d,files in os.walk(path):
            for f in files:
                if match(pattern, f):
                    goodfiles.append(os.path.join(r,f))
    else:
        files = os.listdir(path)
        r = path
        for f in files:
            if match(pattern, f):
                 goodfiles.append(os.path.join(r,f))
    return goodfiles

def Datapathtestcompiler(textfile, testfile, data_width, nr_of_tests, fulldatapath=True):
    op_width = OP_WIDTH

    # all operations
    loadmem = pattern((('mode', 'LOADMEM'),))
    datamem = pattern((('mode', 'DATAMEM'),))
    checkmem = pattern((('mode', 'CHECKMEM'),))
    end = pattern((('mode', 'END'),))
    checkline1 = pattern((('reg', register()+r'\s*:'), ('value', binarypattern(data_width))))
    checkline2 = pattern((('reg', register()+r'\s*:'), ('value', integerpattern())))
    checkline3 = pattern((('reg', r'pc\s*:'), ('value', binarypattern(data_width))))
    checkline4 = pattern((('reg', r'pc\s*:'), ('value', integerpattern())))
    valueline = pattern((('imm', integerpattern()),))
    bvalueline = pattern((('imm', binarypattern(data_width)),))
    labeldecl = pattern((('label', labelpattern()+":"), ('remainder', r'.*')))
    skipline = pattern([])

    operations = DP_OPERATIONS
    if fulldatapath: operations += FULL_DP_OPERATIONS

    # quick first parse pass: we want to put all labels in a symboltable
    symboltables = dict()
    f = open(textfile, 'r')
    mode = "idle"
    testnr = 0
    line = f.readline()
    import os
    while len(line) > 0:
        if not (line == "\n" or line == os.linesep or skipline.search(line)):
            if mode == "idle":
                if loadmem.search(line):
                    mode = "loadmem"
                    testnr += 1
                    curtestfile = testfile+str(testnr)
                    symboltables[curtestfile] = dict() # start a new test program, and a new debug trace
                    programlinenr = 0
            elif mode == "ignore":
                if loadmem.search(line): mode = "loadmem"
                elif end.search(line): mode = "idle"
            elif mode == "loadmem":
                if datamem.search(line): mode = "ignore"
                elif checkmem.search(line): mode = "ignore"
                elif end.search(line): mode = "idle"
                else:
                    m = labeldecl.search(line)
                    if m:
                        symboltables[curtestfile][m.group("label").strip().strip(":")] = programlinenr
                    programlinenr += 1
        line = f.readline()
    f.close()

    # second pass: parse content
    def process_constant(m):
        return int2bin(m.group('imm'), data_width)
    f = open(textfile, 'r')
    mode = "idle"
    debugtraces = dict()
    testnr = 0
    linenr = 1
    line = f.readline()
    while len(line) > 0:
        if not (line == "\n" or line == os.linesep or skipline.search(line)):
            if mode == "idle":
                if loadmem.search(line):
                    #print "change to loadmem"
                    mode = "loadmem"
                    testnr += 1
                    curtestfile = testfile+str(testnr)
                    debugtraces[curtestfile] = dict() # start a new test program, and a new debug trace
                    programlinenr = 0
            elif mode == "loadmem":
                matched = None
                matcheddesc = None
                if datamem.search(line):
                    if programlinenr == 0:
                        print("warning: line %d: wanted to start a data section, but expects instructions first" % linenr)
                    programlinenr += 1
                    debugtraces[curtestfile][programlinenr] = {"linenr": linenr, "line": "STOP", "bin": "0"*op_width, "hex": ubin2hex("0"*op_width, op_width), "name": "STOP", "checks": dict()}
                    #print "change to datamem"
                    mode = "datamem"
                elif checkmem.search(line):
                    if programlinenr == 0:
                        print("warning: line %d: wanted to start a check section, but expects instructions first" % linenr)
                    #print "change to checkmem"
                    mode = "checkmem"
                elif end.search(line):
                    #print "change to idle"
                    mode = "idle"
                else:
                    programlinenr += 1
                    # check whether the line contains an instruction
                    for opname, oppattern, opdescription, opparser in operations:
                        m = oppattern.search(line)
                        if m:
                            try:
                                binary = opparser(m, (programlinenr,symboltables[curtestfile]))
                                debugtraces[curtestfile][programlinenr] = {"linenr": linenr, "line": line.strip(), "bin": binary, "hex": ubin2hex(binary, op_width), "name": opname, "checks": dict()}
                            except Exception as e:
                                print("could not parse line %d: '%s' %s" % (linenr, line.strip(), e))
                                del debugtraces[curtestfile]
                                mode = "idle"
                            matched = opname
                            break
                        elif not matcheddesc: # check if line started with a certain operation identifier
                            if re.compile("^\\s*%s\s+" % opname).search(line):
                                matcheddesc = opdescription
                    if not matched:
                        print("line %d not recognized: '%s', but should be of the form: %s"  % (linenr, line.strip(), str(matcheddesc) if matcheddesc else ""))
                        del debugtraces[curtestfile]
                        mode = "idle"
            elif mode == "datamem":
                if end.search(line):
                    #print "change to idle"
                    mode = "idle"
                elif checkmem.search(line):
                    #print "change to checkmem"
                    mode = "checkmem"
                else:
                    programlinenr += 1
                    matched = None
                    for immpattern in [valueline, bvalueline]:
                        m = immpattern.search(line)
                        if m:
                            if immpattern == valueline:
                                if len(m.group('imm')) == data_width:
                                    continue
                                try:
                                    binary = process_constant(m)
                                except ValueError:
                                    continue
                            else:
                                binary = m.group('imm')
                            debugtraces[curtestfile][programlinenr] = {"linenr": linenr, "line": line.strip(), "bin": binary, "hex": ubin2hex(binary, data_width), "name": "imm", "checks": dict()}
                            matched = "imm"
                            break
                    if not matched:
                        print("line %d not recognized: '%s', but should be %d-bit data"  % (linenr, line.strip(), data_width))
                        del debugtraces[curtestfile]
                        mode = "idle"
            elif mode == "checkmem": # insert a check after the last instruction
                if end.search(line):
                    #print "change to idle"
                    mode = "idle"
                elif loadmem.search(line):
                    if fulldatapath:
                        print("warning: when checking the full datapath, only checks at the end of the program will be made")
                    #print "change to loadmem"
                    mode = "loadmem"
                elif datamem.search(line):
                    #print "change to datamem"
                    programlinenr += 1
                    debugtraces[curtestfile][programlinenr] = {"linenr": linenr, "line": "STOP", "bin": "0"*op_width, "hex": ubin2hex("0"*op_width, op_width), "name": "STOP", "checks": dict()}
                    mode = "datamem"
                else:
                    m = checkline1.search(line)
                    m = checkline2.search(line) if not m else m
                    m = checkline3.search(line) if not m else m
                    m = checkline4.search(line) if not m else m
                    if m:
                        #print "checkline"
                        if len(m.group("value")) == data_width:
                            binval = m.group("value")
                        else:
                            binval = str(int2bin(m.group("value"),data_width))
                        # now add check to last instruction (ignore all data fields)
                        i = programlinenr
                        lastop = debugtraces[curtestfile][i]
                        while lastop["name"] in ["imm", "STOP"]:
                            lastop = debugtraces[curtestfile][i]
                            i -= 1
                        lastop["checks"][0 if m.group("reg") == "pc:" else 1+int(m.group("reg").rstrip(":").lstrip("r"))] = binval
                    else:
                        print("line %d not recognized: '%s', but should be of the form: reg: value"  % (linenr, line.strip()))
                        del debugtraces[curtestfile]
                        mode = "idle"
        line = f.readline()
        #print "%12s   %s" % (mode, line.strip())
        #print "\n".join(["%s : %s" % (key, debugtraces[curtestfile][key]) for key in debugtraces[curtestfile].keys()])
        linenr += 1
    f.close()
    #pprint(debugtraces)

    # write all content to a raw data file
    import os.path
    for curtestfile in debugtraces.keys():
        debugtrace = debugtraces[curtestfile]
        f = open(curtestfile, 'w')
        f.write("v2.0 raw\n")
        traces = debugtraces[curtestfile].keys()
        traces = sorted(traces)
        for i in traces:
            f.write(debugtraces[curtestfile][i]["hex"])
            f.write("\n")
        f.close()

    print("all done: " + textfile)
    return debugtraces

def SimpleDatapathtestcompiler(textfile, testfile, width, nr_of_tests):
    return Datapathtestcompiler(textfile, testfile, width, nr_of_tests, fulldatapath=False)

def Datapathparser(reportfile, debugtrace, width, nr_of_tests, fulldatapath=True):
    #for k in debugtrace.keys(): print k, debugtrace[k]
    # display debug information
    try:
        f = open(reportfile, 'r')
    except IOError:
        print("filename %s not found" % reportfile)
        return False

    #pprint(debugtrace)

    nr_of_tests = 0
    failures = 0
    errors = 0
    lines = f.readlines()
    instructionkeys = [line for line in debugtrace.keys() if not debugtrace[line]["name"] in ["STOP", "imm"]]
    if not fulldatapath and len(lines) <= len(instructionkeys) and len(debugtrace) > 0:
        print("LOGISIM ERROR: Simulation did not return good results - maybe your program loops infinitely on the datapath?\n-- Try executing your program in logisim by loading the generated test file in your RAM-elements and starting clock ticks.")
        return (0,0,0)
    f.close()

    # first check for any errors in output
    for i in range(1, len(lines)):
        line = lines[i]
        items = [item.replace(" ", "").strip() for item in line.split("\t")]
        regnr = -1
        for item in items:
            regname = "pc" if regnr == -1 else "r%d" % regnr
            regnr += 1
            if 'E' in item or 'x' in item:
                if not fulldatapath:
                    curtrace = debugtrace[i]
                    print("Warning: %s has value %s, at line %d: %s" % (regname, item, curtrace["linenr"], curtrace["line"]))
                else:
                    print("Warning: %s has value %s" % (regname, item))

    if not fulldatapath:
        # in simple data path report file starts with dummy line and ends with the halt line (2 lines more than instructions)
        if len(lines) == len(instructionkeys)+1:
            print("Warning: report file %s should have %d lines but has %d lines" % (reportfile, len(instructionkeys)+2, len(lines)))
        assert len(lines) == len(instructionkeys)+1 or len(lines) == len(instructionkeys)+2, "Report file %s should have %d lines but has %d lines (this is due to a Logisim error. Possible cause: you used multiple clock instances in your (sub)circuits, whereas you should only use a single clock instance. -- Contact the author of this Python program for help)"% (reportfile, len(instructionkeys)+2, len(lines))

    for i in range(1, len(instructionkeys)+1): # start counting from 1
        curtrace = debugtrace[i]
        checks = debugtrace[i]["checks"]
        # then go over the checks if present
        if (len(checks) > 0) and (not fulldatapath or i == len(instructionkeys)): # only check last instruction in case of a full datapath, otherwise we're in trouble in case of a loop
            if not fulldatapath:
                line = lines[i]
            else:
                line = lines[-2] # the second to last, because the last one is the one we already halted (pc will be increased)
                # ok, in two cases there is no additional next state, so we will need to look at lines[-1]
                if line.split("\t")[1:] != lines[-1].split("\t")[1:]: # register values did change last step
                    line = lines[-1]
                elif int(line.split("\t")[0].replace(" ", "").strip(), 2)+1 != int(lines[-1].split("\t")[0].replace(" ", "").strip(), 2): # last step was a branch
                    line = lines[-1]
            items = [item.replace(" ", "").strip() for item in line.split("\t")]
            if fulldatapath:
                final_pc = int(items[0], 2)
                # only if last instruction is not a branch instruction:
                # assert final_pc == len(instructionkeys), "PC value at final instruction should be %d but is %d"% (len(instructionkeys), final_pc)
            for reg in checks.keys():
                nr_of_tests += 1
                oracle = checks[reg]
                value = items[reg]
                regname = "pc"
                if reg >= 1: regname = "r%d" % (reg-1)
                if 'E' in value or 'x' in value:
                    errors += 1
                    print("Error: %s has value %s, at line %d: %s" % (regname, value, curtrace["linenr"], curtrace["line"]))
                elif oracle != value:
                    if int(value, 2)+1==int(oracle, 2) and regname == "pc" and not line == lines[-1]: # it may still be true that we actually need to look at the last entry... just throw warning
                        print("Warning: pc may not have been increased yet (expected %s, got %s)" % (oracle, value))
                    else:
                        failures += 1
                        print("Failure: %s must be %s, but is %s, at line %d: %s" % (regname, oracle, value, curtrace["linenr"], curtrace["line"]))

    return (nr_of_tests, errors, failures)

def SimpleDatapathparser(reportfile, debugtrace, width, nr_of_tests):
    return Datapathparser(reportfile, debugtrace, width, nr_of_tests, fulldatapath=False)


def ALUtestcompiler(textfile, testfile, width, nr_of_tests):
    # compiler for ALU tests

    # operations
    operations = ALU_OPERATIONS.keys()

    # read all content to a list
    filecontent = []
    debugtrace = dict()
    linenr = 0
    f = open(textfile, 'r')
    for line in f.readlines():
        params = line.split()
        newparams = []
        if len(params) == 0:
            # empty line, skip
            continue
        linenr +=1
        op = params[0].lower()
        if op in operations:
            newparams.append("%x" % int(ALU_OPERATIONS[op][0]))
        else:
            print("Unable to parse, did not find valid operation %s: %s" % (str(operations), line))
            return False
        # some syntax checks of the parameters
        for param in params[1:4]:
            try:
                if not (len(param) == width): # if its not a binary string...
                    if (int(param) > 2**(width-1)-1 or int(param) < -(2**(width-1))):
                        print("Number exceeds supported ALU range of [%d, %d] on line %d: %s" % (-(2**(width-1)), 2**(width-1)-1, linenr, line))
                        return False
                else:
                    try:
                        dec2twoscompl_hex(param, width)
                    except Exception:
                        print("Expected a binary string, but got %s, on line: %s" % (param, line))
                        return False
            except Exception as e:
                print("Line does not have the right format: %s" % line)
                return False
        for param in params[4:]:
            try:
                if not int(param) in [0,1]:
                    print("Parameter denoting that there should/shouldn't be an error must be 1 or 0, but is %s in line %s" % (param, line))
                    return False
            except Exception:
                print("Parameter denoting that there should/shouldn't be an error must be 1 or 0, but is %s in line %s" % (param, line))
                return False
        # add all parameters
        newparams += [dec2twoscompl_hex(s, width) for s in params[1:]]
        while len(newparams) < 8:
            newparams.append('0')
        newline = "%s %s %s %s %s %s %s %s\n" % (newparams[0],newparams[1],newparams[2],newparams[3],newparams[4],newparams[5],newparams[6],newparams[7])
        filecontent.append(newline)
        debugtrace[linenr] = [line, newline]
        if linenr == nr_of_tests:
            print("MAXIMUM NUMBER OF TESTS (%d) REACHED! IGNORING FURTHER TESTS. (You can split up your tests over two test files.)" % nr_of_tests)
            break

    f.close()

    # add a delimiter in front of the file to solve the synchronization error
    filecontent = ["0 0 0 0 0 1 0 0\n"] + filecontent

    # write all content to a raw data file
    import os.path
    f = open(testfile, 'w')
    f.write("v2.0 raw\n")
    for line in filecontent:
        f.write(line)
    f.close()

    print("all done: " + textfile)
    return {testfile: debugtrace}


def ALUparser(reportfile, debugtrace, width, nr_of_tests):
    # display debug information
    try:
        f = open(reportfile, 'r')
    except IOError:
        print("filename %s not found" % reportfile)
        return False
    lines = f.readlines()

    # skip until after delimiter
    linenr = 0
    while linenr <= len(debugtrace):
        if int(lines[linenr].split("\t")[-1]) == 1:
            # delimiter found! skip until here
            lines = lines[linenr+1:len(debugtrace)+linenr+1]
            break
        linenr +=1

    #pprint(debugtrace)
    #pprint(lines)

    failures = 0
    errors = 0
    linenr = 0
    zerary_ops = [op for op in ALU_OPERATIONS.keys() if ALU_OPERATIONS[op][1] == 0]
    unary_ops = [op for op in ALU_OPERATIONS.keys() if ALU_OPERATIONS[op][1] == 1]
    binary_ops = [op for op in ALU_OPERATIONS.keys() if ALU_OPERATIONS[op][1] == 2]

    COUNTER = 0 # 9 bit
    OP = 1 # REGISTER_ADDRESS_SIZE bit
    A = 2 # DATA_WIDTH bit
    B = 3 # DATA_WIDTH bit
    ORACLE = 4 # DATA_WIDTH bit
    RESULT = 5 # DATA_WIDTH bit
    ERR_ORACLE = 6 # 1 bit
    ERROR = 7 # 1 bit
    OK = 8 # 1 bit
    START_DELIMITER = 9 # 1 bit

    while linenr <= len(debugtrace)-1:
        # (FIXED) FIXME: for some students the two following lines had to be switched/-1 deleted because failure messages got messed up... this is the original setup
        linenr += 1
        line = lines[linenr-1] # the line numbers of the debugtrace start counting at 1
        #print(debugtrace[linenr][0], debugtrace[linenr][1], line, "--------")
        cells = line.split("\t")
        if 'E' in line or 'x' in line:
            errors += 1
            print("-- Test on line %d error" % linenr)
            #print line,
            #print debugtrace[linenr][1],
            if debugtrace[linenr][0].split()[0] in zerary_ops:
                op = "Operation %s ('%s'), result is %s, error code is %s" % (cells[OP], debugtrace[linenr][0].split()[0], cells[RESULT], cells[ERROR])
            elif debugtrace[linenr][0].split()[0] in unary_ops:
                op = "Operation %s ('%s') with operand %s (%s), result is %s, error code is %s" % (cells[OP], debugtrace[linenr][0].split()[0], cells[A], debugtrace[linenr][0].split()[1], cells[RESULT], cells[ERROR])
            elif debugtrace[linenr][0].split()[0] in binary_ops:
                op = "Operation %s ('%s') with operands %s (%s) and %s (%s), result is %s, error code is %s" % (cells[OP], debugtrace[linenr][0].split()[0], cells[A], debugtrace[linenr][0].split()[1], cells[B], debugtrace[linenr][0].split()[2], cells[RESULT], cells[ERROR])
            else:
                op = "Unknown operation..."
            print("%s%s" % (str(debugtrace[linenr][0]), op))
            print("")
        elif int(cells[OK]) == 0:
            failures += 1
            print("-- Test on line %d failure" % linenr)
            #print line,
            #print debugtrace[linenr][1],
            if debugtrace[linenr][0].split()[0] in zerary_ops:
                op = "Operation %s ('%s'), result is %s (%s)" % (cells[OP], debugtrace[linenr][0].split()[0], cells[RESULT], twoscompl_bin2dec(cells[RESULT], width))
            elif debugtrace[linenr][0].split()[0] in unary_ops:
                op = "Operation %s ('%s') with operand %s (%s), result is %s (%s)" % (cells[OP], debugtrace[linenr][0].split()[0], cells[A], debugtrace[linenr][0].split()[1], cells[RESULT], twoscompl_bin2dec(cells[RESULT], width))
            elif debugtrace[linenr][0].split()[0] in binary_ops:
                op = "Operation %s ('%s') with operands %s (%s) and %s (%s), result is %s (%s)" % (cells[OP], debugtrace[linenr][0].split()[0], cells[A], debugtrace[linenr][0].split()[1], cells[B], debugtrace[linenr][0].split()[2], cells[RESULT], twoscompl_bin2dec(cells[RESULT], width))
            else:
                op = "Unknown operation..."
            if int(cells[ERROR]) == 1:
                op += " yielded an EXCEPTION"
            if int(cells[ERROR]) != int(cells[ERR_ORACLE]):
                print("%s%s" % (str(debugtrace[linenr][0]), op))
                print("Expected %s as exception signal, but got %s" % (cells[ERR_ORACLE], cells[ERROR]))
            if int(cells[ERR_ORACLE]) == 0 and cells[RESULT] != cells[ORACLE]: # results are only compared when no error is raised (int(cells[ERR_ORACLE]) == 0)
                print("%s%s" % (str(debugtrace[linenr][0]), op))
                print("Expected %s (%d) as result, but got %s (%d)" % (cells[ORACLE], twoscompl_bin2dec(cells[ORACLE]), cells[RESULT], twoscompl_bin2dec(cells[RESULT])))
            print("")

    return (linenr, errors, failures)

process = None
def Test(textfile, circfile, compiler, parser, logisim):
    width = DATA_WIDTH # width of one data word
    nr_of_tests = 2**12

    if not os.path.isfile(textfile):
        print("%s not found in %s" % (textfile, os.getcwd()))
        return False
    if not os.path.isfile(circfile):
        print("%s not found in %s" % (circfile, os.getcwd()))
        return False

    # delete all absolute paths in circ file (recursively: also in referenced circ files):
    circfilepattern = re.compile(r'^\s*\<lib desc="file#(?P<path>.*)" name="\d+"/\>\s*$')
    abspathpattern = re.compile(r'^\s*\<lib desc="file#.*[\\/]\w*\.circ" name="\d+"/\>\s*$')
    def remove_absolute_paths_from_circ_file(filename):
        if not os.path.isfile(filename):
            os.chdir(startdir)
            raise ValueError("%s could not be found in %s" % (filename, os.getcwd()))
        f = open(filename, 'r')
        reffiles = []
        content = ""
        for line in f.readlines():
            m = circfilepattern.search(line)
            if m:
                path = m.group("path")
                reffile = path.split("\\")[-1].split("/")[-1]
                reffiles.append(reffile) # DO NOT use os.path.basename because it uses the pathseparator of your current os
                if path != reffile:
                    print("In %s: replacing \"%s\" by \"%s\"" % (filename, path, reffile))
                    line = line.replace(path, reffile)
            content += line
        f.close()
        f = open(filename, 'w')
        f.write(content)
        f.close()
        for reffile in reffiles:
            remove_absolute_paths_from_circ_file(reffile)
    startdir = os.getcwd()
    path, filename = os.path.split(circfile)
    if path: os.chdir(path)
    try:
        remove_absolute_paths_from_circ_file(filename)
    except ValueError as e:
        print(e)
        return False
    if path: os.chdir(startdir)

    testfile = os.path.join(path, os.path.splitext(os.path.split(textfile)[1])[0] + ".test")
    errorfile = os.path.join(path, os.path.splitext(os.path.split(textfile)[1])[0] + ".error")

    debugtraces = compiler(textfile, testfile, width, nr_of_tests)

    if not debugtraces:
        print("Error reading test file %s" % testfile)
        return False

    # run the tests with logisim
    print("starting tests...")

    result = True
    testfiles = debugtraces.keys()
    if (len(testfiles) > 1):
        testfiles = sorted(testfiles, key=lambda f: int(f[len(testfile):]))
    for testfile in testfiles:
        debugtrace = debugtraces[testfile]
        reportfile = os.path.splitext(testfile)[0] + os.path.splitext(testfile)[1].replace("test", "report")
        print("")
        print("testing %s --> %s" % (testfile, reportfile))
        #command = "java -jar %s %s -tty table -load %s > %s" % (logisim, circfile, testfile, reportfile)
        #print(command)
        f = open(reportfile, 'w')
        f2 = open(errorfile, 'w')
        if TIMEOUT <= 0:
            import subprocess
            p = subprocess.Popen(["java", "-jar", logisim, circfile, "-tty", "table", "-load", testfile], stdout=f, stderr=f2)
            p.wait()
        else:
            import subprocess, threading
            def target():
                global process
                process = subprocess.Popen(["java", "-jar", logisim, circfile, "-tty", "table", "-load", testfile], stdout=f, stderr=f2)
                process.communicate()
            thread = threading.Thread(target=target)
            thread.start()
            if TIMEOUT > 0:
                if compiler ==  ALUtestcompiler:
                    thread.join()
                else:
                    thread.join(TIMEOUT)
                    if thread.is_alive():
                        process.terminate()
                        thread.join()
                        print("Terminating Logisim after %ds. Infinite loop?" % TIMEOUT)
                        continue

        f.close()
        f2.close()
        # check whether logisim produced an error; stderr was redirected to f2
        f2 = open(errorfile, 'r')
        lines = f2.readlines()
        f2.close()
        if len(lines) > 0:
            print("Logisim verification failed, the following error occurred:")
            for l in lines: print(">>> %s" % l)
            os.remove(errorfile)
            result = False
            continue
        else:
            os.remove(errorfile)

        # parse results
        (nr_of_tests, errors, failures) = parser(reportfile, debugtrace, width, nr_of_tests)

        print("%d tests done, %d errors, %d failures" % (nr_of_tests, errors, failures))
    return result

def main():
    if __name__ == "__main__":
        parser = ArgumentParser()
        parser.add_argument("-a", "--alu", action="store_true", dest="alu", help="test the ALU")
        parser.add_argument("-s", "--simpledatapath", action="store_true", dest="sdp", help="test simple datapath (only r-type and sb/lb)")
        parser.add_argument("-f", "--fulldatapath", action="store_true", dest="fdp", help="test full datapath (all instructions)")
        parser.add_argument("-c" ,"--circuit", type=str, dest="circuit", help="<file_to_test.circ>")
        parser.add_argument("-i", "-t", "--input", "--test", type=str, dest="testfile", help="<file_to_compile.txt>")
        parser.add_argument("--logisimpath", type=str, dest="path", default="logisim-generic-2.7.1.jar", help="sets logisim jar to <PATH>")
        parser.add_argument("--timeout", type=int, dest="timeout", default="20", help="sets the timeout in seconds for infinite loops to TIMEOUT (0 means no timeout) (default: 20s)")
        args = parser.parse_args()

        logisim = args.path
        global TIMEOUT
        TIMEOUT = args.timeout

        if args.alu:
            compiler = ALUtestcompiler
            parser = ALUparser
        elif args.sdp:
            compiler = SimpleDatapathtestcompiler
            parser = SimpleDatapathparser
        elif args.fdp:
            compiler = Datapathtestcompiler
            parser = Datapathparser
        else:
            exit(1)

        try:
            textfile = args.testfile
            f = open(textfile, 'r')
        except IOError:
            print("filename %s not found" % textfile)
            exit(1)
        try:
            circfile = args.circuit
            f = open(circfile, 'r')
            f.close()
        except IOError:
            print("filename %s not found" % circfile)
            exit(1)

        if not Test(textfile, circfile, compiler, parser, logisim):
            exit(1)


"""
Parameters:
"""

# timeout in seconds of logisim
TIMEOUT = 20

# logisim filename
logisim = "logisim-generic-2.7.1.jar"

# width of a data word
DATA_WIDTH = 16

# width of an operation
OP_WIDTH = 16

# size of a register address, number of registers is REGISTER_ADDRESS_SIZE**2
REGISTER_ADDRESS_SIZE = 4

# set of the read-only registers numbers
READONLY_REGISTERS = {0, 15}

# operations supported by the ALU (are all parsed the same: "op x y z", where op is the operation, x is the 1st term, y is the 2nd term z is the oracle)
# items: op_name: (opcode, #terms)
ALU_OPERATIONS = {
'zero': (int('0000', 2),  0),
'not':  (int('0001', 2),  1),
'and':  (int('0010', 2),  2),
'or':   (int('0011', 2),  2),
'add':  (int('0100', 2),  2),
'sub':  (int('0101', 2),  2),
'lt':   (int('0110', 2),  2),
'gt':   (int('0111', 2),  2),
'eq':   (int('1000', 2),  2),
'neq':  (int('1001', 2),  2),
'inv':  (int('1010', 2),  1),
'sll':  (int('1011', 2),  1),
'srl':  (int('1100', 2),  1),
'sla':  (int('1101', 2),  1),
'sra':  (int('1110', 2),  1),
'noop': (int('1111', 2),  1)
}

# simple data path operations for project 5 (typically alu ops + lb, sb)
# (name, parse_pattern, help_string, compile_function)
DP_OPERATIONS = [
('zero' , pattern((('op', 'zero'), ('rd', register())), can_have_label=True),                                                       "zero rd            -->  $rd := 0",                          lambda m, params : '0000'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+'0000'+'0000' ),
('not'  , pattern((('op', 'not'),  ('rd', register()), ('rs', register())), can_have_label=True),                                   "not rd rs          -->  $rd := ! $rs",                      lambda m, params : '0001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+'0001' ),
('inv'  , pattern((('op', 'inv'),  ('rd', register()), ('rs', register())), can_have_label=True),                                   "inv rd rs          -->  $rd := - $rs",                      lambda m, params : '0001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+'1010' ),
('sll'  , pattern((('op', 'sll'),  ('rd', register()), ('rs', register())), can_have_label=True),                                   "sll rd rs          -->  $rd := $rs << 2",                   lambda m, params : '0001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+'1011' ),
('srl'  , pattern((('op', 'srl'),  ('rd', register()), ('rs', register())), can_have_label=True),                                   "srl rd rs          -->  $rd := $rs >> 2",                   lambda m, params : '0001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+'1100' ),
('sla'  , pattern((('op', 'sla'),  ('rd', register()), ('rs', register())), can_have_label=True),                                   "sla rd rs          -->  $rd := $rs * 2",                    lambda m, params : '0001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+'1101' ),
('sra'  , pattern((('op', 'sra'),  ('rd', register()), ('rs', register())), can_have_label=True),                                   "sra rd rs          -->  $rd := $rs / 2",                    lambda m, params : '0001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+'1110' ),
('cp'   , pattern((('op', 'cp'),   ('rd', register()), ('rs', register())), can_have_label=True),                                   "cp rd rs           -->  $rd := $rs",                        lambda m, params : '0001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+'1111' ),
('and'  , pattern((('op', 'and'),  ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "and rd rs rt       -->  $rd := $rs & $rt",                  lambda m, params : '0010'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('or'   , pattern((('op', 'or'),   ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "or rd rs rt        -->  $rd := $rs | $rt",                  lambda m, params : '0011'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('add'  , pattern((('op', 'add'),  ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "add rd rs rt       -->  $rd := $rs + $rt",                  lambda m, params : '0100'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('sub'  , pattern((('op', 'sub'),  ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "sub rd rs rt       -->  $rd := $rs - $rt",                  lambda m, params : '0101'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('lt'   , pattern((('op', 'lt'),   ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "lt rd rs rt        -->  $rs < $rt ? $rd := 1 : $rd := 0",   lambda m, params : '0110'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('gt'   , pattern((('op', 'gt'),   ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "gt rd rs rt        -->  $rs > $rt ? $rd := 1 : $rd := 0",   lambda m, params : '0111'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('eq'   , pattern((('op', 'eq'),   ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "eq rd rs rt        -->  $rs = $rt ? $rd := 1 : $rd := 0",   lambda m, params : '1000'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('neq'  , pattern((('op', 'neq'),  ('rd', register()), ('rs', register()), ('rt', register())), can_have_label=True),               "neq rd rs rt       -->  $rs != $rt ? $rd := 1 : $rd := 0",  lambda m, params : '1001'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rt'),REGISTER_ADDRESS_SIZE)) ),
('lw'   , pattern((('op', 'lw'),   ('rd', register()), ('rs', register()), ('imm', integerpattern())), can_have_label=True),        "lw rd rs uimm      -->  $rd := MEM[$rs + imm]",             lambda m, params : '1010'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),4)) ),
('sw'   , pattern((('op', 'sw'),   ('rd', register()), ('rs', register()), ('imm', integerpattern())), can_have_label=True),        "sw rd rs uimm      -->  MEM[$rs + imm] := $rd",             lambda m, params : '1011'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),4)) )
]

# extra full data path operations
# (name, parse_pattern, help_string, compile_function)
FULL_DP_OPERATIONS = [
('ori'  , pattern((('op', 'ori'),  ('rd', register()), ('imm', binarypattern(8))), can_have_label=True),                            "ori rs imm     -->  rd := rd | imm",               lambda m, params : '1100'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+m.group('imm') ),
('ori'  , pattern((('op', 'ori'),  ('rd', register()), ('imm', uintegerpattern())), can_have_label=True),                           "ori rs imm     -->  rd := rd | imm",               lambda m, params : '1100'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),8)) ),
('lui'  , pattern((('op', 'lui'),  ('rd', register()), ('imm', binarypattern(8))), can_have_label=True),                            "lui rs imm     -->  rd := imm << 6",               lambda m, params : '1101'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+m.group('imm') ),
('lui'  , pattern((('op', 'lui'),  ('rd', register()), ('imm', uintegerpattern())), can_have_label=True),                           "lui rs imm     -->  rd := imm << 6",               lambda m, params : '1101'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),8)) ),
#('addi' , pattern((('op', 'addi'), ('rd', register()), ('imm', binarypattern(6))), can_have_label=True),                            "addi rd imm -->  rd := rd + imm",                  lambda m, params : '100'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+m.group('imm')+'0100'),
#('addi' , pattern((('op', 'addi'), ('rd', register()), ('imm', uintegerpattern())), can_have_label=True),                           "addi rd imm -->  rd := rd + imm",                  lambda m, params : '100'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(uint2bin(m.group('imm'),6))+'0100'),
#('subi' , pattern((('op', 'subi'), ('rd', register()), ('imm', binarypattern(6))), can_have_label=True),                            "subi rd imm -->  rd := rd + imm",                  lambda m, params : '100'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+m.group('imm')+'0101'),
#('subi' , pattern((('op', 'subi'), ('rd', register()), ('imm', uintegerpattern())), can_have_label=True),                           "subi rd imm -->  rd := rd + imm",                  lambda m, params : '100'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(uint2bin(m.group('imm'),6))+'0101'),
#('beq'  , pattern((('op', 'beq'),  ('rd', register()), ('rs', register()), ('imm', integerpattern())), can_have_label=True),        "beq rd rs imm   -->  rd==rs ? pc := pc+1+imm",     lambda m, params : '101'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),6))+'0' ),
#('beq'  , pattern((('op', 'beq'),  ('rd', register()), ('rs', register()), ('to', labelpattern())), can_have_label=True),           "beq rd rs imm   -->  rd==rs ? pc := pc+1+imm",     lambda m, params : '101'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(label2bin(m.group('to'),6,params[1],params[0]-1))+'0' ),
#('blt'  , pattern((('op', 'blt'),  ('rd', register()), ('rs', register()), ('imm', integerpattern())), can_have_label=True),        "blt rd rs imm   -->  rd<rs ? pc := pc+1+imm",      lambda m, params : '101'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),6))+'1' ),
#('blt'  , pattern((('op', 'blt'),  ('rd', register()), ('rs', register()), ('to', labelpattern())), can_have_label=True),           "blt rd rs imm   -->  rd<rs ? pc := pc+1+imm",      lambda m, params : '101'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(reg2bin(m.group('rs'),REGISTER_ADDRESS_SIZE))+str(label2bin(m.group('to'),6,params[1],params[0]-1))+'1' ),
('brnz' , pattern((('op', 'brnz'), ('rd', register()),  ('imm', integerpattern())), can_have_label=True),                           "brnz rd imm     -->  rd!=0 ? pc := pc+1+imm",      lambda m, params : '1110'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),8)) ),
('brnz' , pattern((('op', 'brnz'), ('rd', register()),  ('to', labelpattern())), can_have_label=True),                              "brnz rd imm     -->  rd!=0 ? pc := pc+1+imm",      lambda m, params : '1110'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(label2bin(m.group('to'),8,params[1],params[0]-1)) ),
('j'    , pattern((('op', 'j'),    ('addr', binarypattern(8))), can_have_label=True),                                               "j addr          -->  pc := addr",                  lambda m, params : '1111'+m.group('addr')+'0000' ),
('j'    , pattern((('op', 'j'),    ('addr', uintegerpattern())), can_have_label=True),                                              "j addr          -->  pc := addr",                  lambda m, params : '1111'+str(int2bin(m.group('addr'),8))+'0000' ),
('j'    , pattern((('op', 'j'),    ('to', labelpattern())), can_have_label=True),                                                   "j addr          -->  pc := addr",                  lambda m, params : '1111'+str(label2bin(m.group('to'),8,params[1]))+'0000' ),
('jr'   , pattern((('op', 'jr'),   ('rd', register()), ('imm', binarypattern(4))), can_have_label=True),                            "jr rd imm       -->  pc := rd+imm",                lambda m, params : '1111'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+m.group('imm')+'0100' ),
('jr'   , pattern((('op', 'jr'),   ('rd', register()), ('imm', integerpattern())), can_have_label=True),                            "jr rd imm       -->  pc := rd+imm",                lambda m, params : '1111'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(int2bin(m.group('imm'),4))+'0100' ),
('jr'   , pattern((('op', 'jr'),   ('rd', register()), ('to', labelpattern())), can_have_label=True),                               "jr rd imm       -->  pc := rd+imm",                lambda m, params : '1111'+str(reg2bin(m.group('rd'),REGISTER_ADDRESS_SIZE))+str(label2bin(m.group('to'),4,params[1]))+'0100' ),
('jal'  , pattern((('op', 'jal'),  ('addr', binarypattern(8))), can_have_label=True),                                               "jal addr        -->  r7 := pc+1 ; pc := addr",     lambda m, params : '1111'+m.group('addr')+'1111' ),
('jal'  , pattern((('op', 'jal'),  ('addr', uintegerpattern())), can_have_label=True),                                              "jal addr        -->  r7 := pc+1 ; pc := addr",     lambda m, params : '1111'+str(int2bin(m.group('addr'),8))+'1111' ),
('jal'  , pattern((('op', 'jal'),  ('to', labelpattern())), can_have_label=True),                                                   "jal addr        -->  r7 := pc+1 ; pc := addr",     lambda m, params : '1111'+str(label2bin(m.group('to'),8,params[1]))+'1111' ),
]

"""
End Parameters
"""

main()
