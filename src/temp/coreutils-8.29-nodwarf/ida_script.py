from idautils import *
from idc import *
from idaapi import *
import idc, idaapi, idautils, ida_xref
import pickle

def find_stack_members(func_ea):
    members = {}
    base = None
    frame = idc.GetFrame(func_ea)
    try:
        for frame_member in idautils.StructMembers(frame):
            member_offset, member_name, size = frame_member
            members[member_offset] = size
            if member_name == ' s':
                base = member_offset
        if not base:
          base = 3
    except:
        return 0, 0
    return members, base

def calc_offset(mems, base, fName):
    data = []
    for i in mems:
        off = i - base
        if off >= 0: continue
        data.append([off, mems[i]])
    return data

def find_stack_xrefs(func_offset, fName):
    func_ea = ida_funcs.get_func(func_offset).startEA
    members, stack_base = find_stack_members(func_ea)
    if members == 0:
        return 0
    datas = calc_offset(members, stack_base, funcName)
    return datas

if __name__ == "__main__":
    autoWait()
    ea = BeginEA()
    alocs = {}
    for funcAddr in Functions(SegStart(ea), SegEnd(ea)):
        funcName = GetFunctionName(funcAddr)
        datas = find_stack_xrefs(funcAddr, funcName)
        if datas ==0: print("error")
        else: alocs[funcName] = datas
    f = open(idc.ARGV[1],"w")
    pickle.dump(alocs,f)
    f.close()
    Exit(0)

