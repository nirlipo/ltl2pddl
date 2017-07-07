#!/usr/bin/python

import os
import sys

for i in range(100,4100,100):
    os.system("./waldo_generator "+str(i)+" sequential > waldo-seq-"+str(i)+".pddl")
    print "./waldo_generator "+str(i)+" sequential > waldo-seq-"+str(i)+".pddl"

for i in range(100,4100,100):
    os.system("./waldo_generator "+str(i)+" cross > waldo-cross-"+str(i)+".pddl")
    print "./waldo_generator "+str(i)+" cross > waldo-cross-"+str(i)+".pddl"
