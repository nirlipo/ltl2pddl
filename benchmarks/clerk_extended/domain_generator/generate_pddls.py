#!/usr/bin/python

import os
import sys

for i in range(1,21):
     os.system("./packages_generator "+str(i)+" sequential > packages-seq-"+str(i)+".pddl")
     print "./packages_generator "+str(i)+" sequential > packages-seq-"+str(i)+".pddl"

for i in range(1,21):
    os.system("./packages_generator "+str(i)+" cross > packages-cross-"+str(i)+".pddl")
    print "./packages_generator "+str(i)+" cross > packages-cross-"+str(i)+".pddl"
