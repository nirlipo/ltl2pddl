#!/usr/bin/python

import os
import sys

for i in range(1,21):
    os.system("./lift_generator "+str(i)+" sequential > lift-seq-"+str(i)+".pddl")
    print "./lift_generator "+str(i)+" sequential > lift-seq-"+str(i)+".pddl"

for i in range(1,21):
    os.system("./lift_generator "+str(i)+" cross > lift-cross-"+str(i)+".pddl")
    print "./lift_generator "+str(i)+" cross > lift-cross-"+str(i)+".pddl"
