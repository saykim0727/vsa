import os
import subprocess
pwd = os.getcwd() +"/"
files = os.listdir(pwd)
for i in files:
  print (i)
  if "get_dwarf" in i or "main.py" in i: continue
  dwarf_path = "%s/%s.dwarf" % (pwd,i)
  f = open(dwarf_path,"w")
  cmd = ["/usr/bin/python","get_dwarf_info.py", i]
  proc = subprocess.Popen(cmd, stdout = f)
  proc.wait()
  f.close()
