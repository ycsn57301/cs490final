#!/usr/bin/python

import sys
import os
import argparse
import subprocess
# import difflib

global command

argv = sys.argv[2:]

command = "ls %s" % ("-al")
actions_list = ''

basedir = os.path.dirname(os.path.abspath(__file__))

argparser = argparse.ArgumentParser(
    # prog="%s %s" % (os.path.basename(__file__), command),
    # formatter_class=argparse.RawTextHelpFormatter,
    # epilog="actions_desc",
)

argparser.add_argument("--prog", "-p", help="specify the program inside the `examples` directory")
argparser.add_argument("--cuts", "-c", help="number of cuts")
argparser.add_argument("--build", "-b", action='store_true', help="flag specifying whether we should create and build")
argparser.add_argument("--paste", "-t", action='store_true', help="flag specifying whether parts should be executed or simply have commands be pasted in the console")

args = vars(argparser.parse_args())

program_name = args["prog"]
num_cuts = int(args["cuts"])
build = args["build"]
print_cmd = args["paste"]



directory = './path/to/make/scripts'
prover_dir = basedir + "/" + program_name+"_prover/"
verifier_dir = basedir + "/" + program_name+"_verifier/"

if (build):
    com1 = "dune exec -- ou cut --proto examples/%s.ou --noc %d" % (program_name, num_cuts)
    os.system(com1)
    
    com2 = "dune exec -- ou eval --input examples/%s.in.ou --proverdir %s_prover/" % (program_name, program_name)
    os.system(com2)

    build_command = 'make'

    os.system('cd {} && {}'.format(prover_dir, build_command))
    os.system('cd {} && {}'.format(verifier_dir, build_command))


starting_port = 12345

tot_cmd_p = ""
tot_cmd_v = ""

if (print_cmd):
    # with this option the commands will be printed but not executed
    single_cmd = ""
    for i in range(num_cuts):
        port = str(12345+i)
        part_cmd_p = " { cd " + prover_dir + " ; ./part"+str(i) + " " + port + " ; } "
        part_cmd_v = " { cd " + verifier_dir + " ; time ./part"+str(i) + " " + port + " ; } "

        single_cmd += " { " + part_cmd_p + " & " + part_cmd_v + " ; } "

        if (i < num_cuts-1):
            single_cmd += " ; "

    print(single_cmd + " ; cd " + basedir)

else:
    # otherwise the commands are executed
    os.system('mkdir data')

    for i in range(num_cuts):
        port = str(12345+i)
        part_cmd = prover_dir+"/part"+str(i)
        subprocess.Popen([part_cmd, port])

    for i in range(num_cuts):
        port = str(12345+i)
        part_cmd = verifier_dir+"/part"+str(i)
        subprocess.Popen(["time",part_cmd, port])
