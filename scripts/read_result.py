#!/usr/bin/env python
# -*- coding: utf-8 -*-

'''
Too many comments ### in the result
omit them when read
'''

import sys

def rm_comment(file_path):
	with open(file_path) as f:
		lines = f.readlines()
		for line in lines:
			if line.strip() != "" and not line.startswith("###") and not line.startswith("Fail to find main package"):
				print(line, end="")
				

if __name__ == "__main__":
	rm_comment(sys.argv[1])
