#!/usr/bin/python

import os
import sys

for i in range(1,21):
    os.system("./packages_prob_generator "+str(i)+" > packages-"+str(i)+".pddl")
    print "./packages_prob_generator "+str(i)+" sequential > packages-"+str(i)+".pddl"
