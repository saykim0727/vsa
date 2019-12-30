import subprocess
import os
import sys
import pickle

def diff_vsa_dwarf(fc,elf_path,vsa_alocs_list, dwarf_alocs, ida_alocs,fname):
  index = 0
  result_path = "%s.result" % (elf_path)
  f = open(result_path,"w")
  f.write(fname)
  f.write("%-30s %+8s %+3s %+3s %+8s %+3s %+3s\n" % ("Func_Name","vsa/dwarf","fit_percent","over_percent","ida/dwarf","fit_percent","over_percent"))
  ida_total_count = 0
  ida_total_perc = 0
  ida_total_over = 0
  total_count = 0
  total_perc = 0
  dwarf_error = 0
  total_over = 0
  func_count = 0
  for vsa_alocs in vsa_alocs_list:
    f.write ("Env %s ------------\n" % index )
    for fname in vsa_alocs.keys():
      if fname == "Global":continue
      over_perc = 0
      fit_perc = 0
      ida_over_perc = 0
      fit_count = 0
      ida_fit_perc = 0
      over_count = 0
      ida_fit_count = 0
      ida_over_count = 0
      if fname not in dwarf_alocs.keys():
        dwarf_error=dwarf_error+1
        continue
      total_count = len(dwarf_alocs[fname])
      func_count +=1
      for aloc in vsa_alocs[fname]:
        if aloc in dwarf_alocs[fname]:
          fit_count = fit_count + 1
        else:
          over_count = over_count + 1

      if fname != "Global":
        if fname in ida_alocs:
          for aloc in ida_alocs[fname]:
            if aloc in dwarf_alocs[fname]:
              ida_fit_count = ida_fit_count + 1
          else:
            ida_over_count = ida_over_count + 1
        else: None

      if total_count != 0:
        fit_perc = fit_count*100/total_count
        ida_fit_perc = ida_fit_count*100/total_count
      if len(vsa_alocs[fname]) != 0:
        over_perc = over_count*100/len(vsa_alocs[fname])
      else: over_perc = 0
      if fname != "Global":
        try:
          if len(ida_alocs[fname]) != 0:
            ida_over_perc = ida_over_count*100/len(ida_alocs[fname])
          else: ida_over_perc = 0
        except: ida_over_perc = 0
      total_perc = total_perc + fit_perc
      total_over = total_over + over_perc
      div = "%s/%s" % (fit_count,total_count)
      ida_total_perc = ida_total_perc + ida_fit_perc
      ida_total_over = ida_total_over + ida_over_perc
      ida_div = "%s/%s" % (ida_fit_count,total_count)
      f.write ("%-30s %+9s %+10s%% %+11s%% %+9s %+10s%% %+11s%%\n" % (fname,div,fit_perc,over_perc,ida_div,ida_fit_perc,ida_over_perc))
    index = index + 1
    if func_count == 0: return [0, 0, 0, 0]
    total_perc = total_perc/func_count
    total_over = total_over/func_count
    ida_total_perc = ida_total_perc/func_count
    ida_total_over = ida_total_over/func_count
    f.write("Dwarf_parsing_error %s\n" % (dwarf_error))
    f.write("Function : %s/%d\n" % (len(vsa_alocs),int(fc)))
    f.write("Total Env : %s%% %s%%\n" % (total_perc, total_over))
    f.write("Total ida : %s%% %s%%\n" % (ida_total_perc, ida_total_over))
  result = [total_perc, total_over, ida_total_perc, ida_total_over]
  f.close()
  return result

def parse_vsa_info(vsa_info):
  # 4.parse aloc of vsa
  aloc_list = []
  fname = "Global"
  data_list = []
  offset = ""
  size = ""
  alocs = {} # {func : [offs, bit]}
  alocs["Global"] = []
  func_num=0
  for line in vsa_info:
    new_line = line.strip().split(" ") #Mem,
    if len(new_line) == "===": #new env
      aloc_list.append(alocs)
      alocs = {}
      fname = ""
      data_list = []
      offset = ""
      size = ""
    elif len(new_line) == 1:
      func_num = int(line.strip())
    elif len(new_line) == 2: #global
      data = new_line[1][1:-1].split(",")
      fname = data[0]
      offset = int(data[1][:-1])
      size = int(data[2])/8
      data_list.append([offset,size])
    else: #local
      data = new_line[2][1:-1].split(",")
      if data[0][1:-1] != fname: #new function
        alocs[fname] = data_list
        if data[0][1:-1] not in alocs:
          data_list = []
        else:
          data_list = alocs[data[0][1:-1]]
      fname = data[0][1:-1]
      offset = int(data[2][:-1])
      size = int(data[3])/8
      data_list.append([offset,size])
  alocs[fname] = data_list
  aloc_list.append(alocs)
  return func_num,aloc_list


def parse_dwarf_info(dwarf_info):
  # 3.make aloc of get_dwarf (offset-16)
  # var = DW_OP_fbreg | DW_OP_addr | ...
  fname = ""
  data = []
  offset = ""
  size = ""
  alocs = {} # {func : [offs, bit]}
  alocs["Global"] = []
  for line in dwarf_info:
    if line == "\n": continue
    elif "(...)" in line: fname = line.split(" ")[2]
    elif ("{" in line): continue
    elif ("}" in line):
      if data == []:
        continue
      else:
        alocs[fname] = data
      data = []
      offset = ""
      size = ""
      fname = ""
    else: #TODO : List variable recovery
      size = int(line.strip().split(" ")[0])
      offset = line.strip().split("(")[1]
      if "DW_OP_fbreg" in offset:
        offset = int(offset.split(" ")[1][:-1])
        if offset >= 0: offset = offset + 16
        else: offset = offset + 16
        data.append([offset,size])
#        if "_[" in line:  #to show our parser is good
#          num = int(line.strip().split("_[")[1].split("]")[0])
#          for i in range(0,int(num)):
#            data.append([offset,size])
#            offset = offset - size
#        else : data.append([offset,size])
      elif "DW_OP_addr" in offset:
        offset = int(offset.split(" ")[1][:-1],16)
        alocs["Global"].append([offset,size])
      elif "DW_OP_reg" in offset:
        continue
      elif ")" not in offset: pass
      else: data.append([offset,size])
  return alocs


def get_ida_info(elf_path):
  pwd = os.getcwd()
  ida_path = "%s/%s.ida" % (pwd, elf_path)
  if os.path.isfile(ida_path) == False:
    f = open(ida_path,"w")
    script = "-S\"%s/ida_script.py\" %s" % (pwd, ida_path)
    cmd = ["/home/kim/ida-6.95/idaq64", "-A", script , elf_path, "-t"]
    proc = subprocess.Popen(cmd, stdout = f)
    proc.wait()
    f.close()
  f = open(ida_path,"rb")
  alocs = pickle.load(f)
  f.close()
  return alocs

def get_vsa_info(elf_path):
  # 2.save vsa
  pwd = os.getcwd()
  vsa_path = "%s/%s.vsa" % (pwd, elf_path)
  if os.path.isfile(vsa_path) == False:
    f = open(vsa_path,"a")
    cmd = ["/usr/bin/dotnet", "run", elf_path]
    proc = subprocess.Popen(cmd, stdout = f)
    try :
      proc.communicate(timeout = 1200)
    except: None
    proc.kill()
    f.close()
  f = open(vsa_path,"r")
  lines = f.readlines()
  f.close()

  return lines

def get_dwarf_info(elf_path):
  # 1.save the result of get_dwarf
  pwd = os.getcwd()
  dwarf_path = "%s/%s.dwarf"  % (pwd,elf_path)
  if os.path.isfile(dwarf_path) == False:
    f = open(dwarf_path,"a")
    cmd = ["/usr/bin/python", "get_dwarf_info.py", elf_path]
    proc = subprocess.Popen(cmd, stdout = f)
    proc.wait()
    f.close()
  f = open(dwarf_path,"r")
  lines = f.readlines()
  f.close()

  return lines

def evaluate_helper(fileName):
  elf_path = fileName
  vsa_info = get_vsa_info(elf_path)

if __name__ == '__main__':
  no_files = ['evaluate_vsa.py','ida_script.py','get_dwarf_info.py','test.fsproj','Program.fs', 'bin', 'obj','.ida','.vsa','.result','.dwarf','i64','test.py']
  # 1.save the result of get_dwarf
  # 2.save vsa
  # 3.make aloc of get_dwarf (offset-16)
  # 4.parse aloc of vsa
  # 5.diff
  result = {}
  pwd = os.getcwd()+"/"
  files = os.listdir(pwd)
  for i in files:
    print(i)
    if i in no_files or "i64" in i or "ida" in i or "vsa" in i or "result" in i or "dwarf" in i:
      continue
    evaluate_helper(i)
