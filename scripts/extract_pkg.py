#!/usr/bin/env python
# -*- coding: utf-8 -*-

'''
Traverse dir to get map["path:pkgName"][goFileList]
usage: ./extract_pkg.py ../tests/bbb
output to data.json
must be exec under current dir
'''

import os
import json
import sys
import subprocess

def get_pkg_name(gofile):
	if os.path.isfile(gofile):
		with open(gofile) as f:
			pkg_name = ""
			while not pkg_name.startswith("package "):
				pkg_name = f.readline()
				pkg_name = pkg_name.strip()

			if pkg_name.startswith("package "):
				pkg_name = pkg_name[8:] 
			pos = pkg_name.find("//")
			if pos != -1:
				pkg_name = pkg_name[:pos]
				pkg_name = pkg_name.strip()
			return pkg_name
	return ""


def extract_pkg(pkg_dirs):
	cmd = '''go list -f '{{.GoFiles}}' '''
	pkg_files = {}
	for pkg_dir in pkg_dirs:
		for dir_name, sub_dir_list, file_list in os.walk(pkg_dir, topdown=True):
			if not "/." in dir_name:
				result = subprocess.run(cmd + dir_name, shell=True, capture_output=True)
				if result.returncode == 0:
					output = result.stdout.decode('utf-8')
					output = output.strip()  # rm '\n'
					raw_output = output[1:-1]
					gofile_list = raw_output.split(' ')

					pkg_name = ""
					for gofile in gofile_list:
						gofilepath = os.path.join(dir_name, gofile)
						if pkg_name == "":
							pkg_name = get_pkg_name(gofilepath)
							# rm "../"
							pkg_files[dir_name + ":" + pkg_name] = [gofilepath[3:]]
						else:
							# rm "../"
							pkg_files[dir_name + ":" + pkg_name].append(gofilepath[3:])

	return pkg_files
						


#def is_other_os(name):
#	other_os_keywords = ["mipsx", "mips64x", "386_test", "nonlinux", "solaris", "plan9", "386", "arm64", "ppc64le", "ppc64", "ppc", "arm", "s390x", "unix_solaris", "openbsd", "windows", "sync_unix"]
#	for k in other_os_keywords:
#		if name.endswith(k + ".go"):
#			return True
#	return False
#
#
#
#def extract_pkg(pkg_dirs):
#	pkg_files = {}
#	for pkg_dir in pkg_dirs:
#		for root, dirs, files in os.walk(pkg_dir, topdown = False):
#			for name in files:
#				if name.endswith(".go"):
#					if not is_other_os(name):
#						file_name = os.path.join(root, name)
#						with open(file_name) as f:
#							#if "vendor/" in file_name:
#							#	continue
#							pkg_name = f.readline()
#							while not pkg_name.startswith("package "):
#								pkg_name = f.readline()
#
#							pos = pkg_name.find("//")
#							if pos != -1:
#								pkg_name = pkg_name[:pos]
#						
#							pkg_name = pkg_name.strip()
#							if pkg_name.startswith("package "):
#								pkg_name = pkg_name[8:]
#								if pkg_name not in pkg_files:
#									pkg_files[pkg_name] = []
#								pkg_files[pkg_name].append(file_name[3:])
#							else:
#								print(file_name, pkg_name)
#
#	return pkg_files


if __name__ == "__main__":
	pkg_files = extract_pkg([sys.argv[1]])
	with open('data.json', 'w') as outfile:
		json.dump(pkg_files, outfile)
