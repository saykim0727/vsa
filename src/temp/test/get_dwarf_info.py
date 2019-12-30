import os
import pickle
import gc
import re
import sys
import itertools
import math
import time
import subprocess

from optparse import OptionParser

from collections import defaultdict
from elftools.common.py3compat import maxint, bytes2str
from elftools.dwarf.descriptions import describe_form_class
from elftools.elf.elffile import ELFFile

import logging, coloredlogs
coloredlogs.install(level=logging.DEBUG)
coloredlogs.install(level=logging.INFO)
import pprint as pp

def get_size(die):
    if 'DW_AT_byte_size' in die.attributes:
      return die.attributes['DW_AT_byte_size'].value
    else: return None

def get_name(die):
    if 'DW_AT_name' in die.attributes:
      return die.attributes['DW_AT_name'].value.decode().replace(" ","")
    else: None

def get_offset(die):
    return die.attributes['DW_AT_location'].value

def has_name(die):
    return 'DW_AT_name' in die.attributes

#def get_sibs(die):
#    assert ('DW_AT_sibling' in die.attributes)
#    return die.attributes['DW_AT_sibling']

def get_type(die):
    assert ('DW_AT_type' in die.attributes)
    return die.attributes['DW_AT_type'].value

def get_upper(die):
    assert ('DW_AT_upper_bound' in die.attributes)
    return die.attributes['DW_AT_upper_bound'].value

def fetch_type(die, type_map, die_list):
    t_ret = []
    if 'DW_AT_type' not in die.attributes:
      return ' '.join(t_ret)
    t_die = type_map[get_type(die)]
    tag = t_die.tag
    name = ""

    if "DW_AT_name" in die.attributes:
        name = die.attributes['DW_AT_name'].value.decode()
        if name in die_list:
            return '_'.join(t_ret)
        else:
          die_list.append(name)

    if tag == 'DW_TAG_base_type':
        t_ret.append("%s %s" % (get_size(t_die),get_name(t_die)))

    elif tag == 'DW_TAG_const_type':
        t_ret.append(fetch_type(t_die, type_map,die_list))

    elif tag == 'DW_TAG_enumeration_type':
        t_ret.append(fetch_type(t_die, type_map, die_list) + 'enum')

    elif tag == 'DW_TAG_pointer_type':
        ty = fetch_type(t_die, type_map, die_list)
        if " " in ty: t_ret.append("8 " + ty.split(" ")[1] + '*')
        else: t_ret.append("8 " + ty + '*')

    elif tag == 'DW_TAG_array_type':
        t_ret.append(fetch_type(t_die, type_map, die_list))
        t_die = next(t_die.iter_children())
        upperbound = get_upper(t_die) + 1
        t_ret.append('[%d]' % upperbound)

    elif tag == 'DW_TAG_union_type':
        tmp = []
        for die in t_die.iter_children():
            assert(die.tag == 'DW_TAG_member')
            tmp.append(fetch_type(die, type_map, die_list) + ' ' + get_name(die))
        t_ret.append('8 {%s;}' % ('; '.join(tmp)))

    elif tag == 'DW_TAG_structure_type':
        tmp = []
        for die in t_die.iter_children():
            assert(die.tag == 'DW_TAG_member')
            if "DW_AT_name" in die.attributes:
              name = die.attributes['DW_AT_name'].value.decode()
              die_list.append(name)
            tmp.append(fetch_type(die, type_map, die_list) + ' ' + get_name(die))
        t_ret.append('%s %s' % (get_size(t_die), (get_name(t_die))))
#        t_ret.append('struct {%s;}' % ('; '.join(tmp)))

    elif tag == 'DW_TAG_typedef':
        tmp = fetch_type(t_die, type_map, die_list)
        size = tmp.split(" ")[0]
        if size == "enum" or size == "None":
          size = 4
        t_ret.append('%s %s' % (size, get_name(t_die)))
#        t_ret.append('{typedef %s %s}' % (fetch_type(t_die, type_map, die_list),
#                                          get_name(t_die), ))

    elif tag == 'DW_TAG_subroutine_type': #TODO
      return '_'.join(t_ret)

    elif tag == 'DW_TAG_restrict_type': #TODO
      t_ret.append(fetch_type(t_die, type_map, die_list))
    elif tag ==  'DW_TAG_volatile_type':
      t_ret.append(fetch_type(t_die, type_map, die_list))
    else:
        print (die)
        print (t_die)
        raise NotImplemented

    #return get_name(t_die) + ' '.join(t_ret)
    return '_'.join(t_ret)


def print_die(CU):
    # Start with the top DIE, the root for this CU's DIE tree
    top_DIE = CU.get_top_DIE()
    print('    Top DIE with tag=%s' % top_DIE.tag)

    # We're interested in the filename...
    print('    name=%s' % top_DIE.get_full_path())

    # Display DIEs recursively starting with top_DIE
    die_info_rec(top_DIE)


def die_info_rec(die, indent_level='    '):
    """ A recursive function for showing information about a DIE and its
        children.
    """
    if has_name(die):
        print(indent_level + 'DIE tag=%s, %s' % (die.tag,
                                                 get_name(die)))
    else:
        print(indent_level + 'DIE tag=%s' % (die.tag))

    child_indent = indent_level + '  '
    for child in die.iter_children():
        die_info_rec(child, child_indent)


def fetch_vars(CU):
    VARIABLE_TAGS = [
        'DW_TAG_variable',
        'DW_TAG_formal_parameter',
    #    'DW_TAG_constant',
    ]
    funcs = {}
    params = defaultdict(list)
    local_vars = defaultdict(list)
    global_vars = []
    type_map = {}
    cu_off = CU.cu_offset
    for die in CU.iter_DIEs():
        if die.is_null():
            continue
        # store type into the dictionary so that it can be fetched easily
        if 'type' in die.tag:
            type_map[die.offset-cu_off] = die

        elif die.tag == 'DW_TAG_subprogram':
            try:
                func_name = get_name(die)
                funcs[func_name] = die
            except:
                #print (die)
                import pdb; pdb.set_trace()

        elif die.tag in VARIABLE_TAGS:
            cur = die
            parent = None
            is_local = False
            while parent is None or \
                    not parent.tag == 'DW_TAG_compile_unit':
                parent = cur.get_parent()
                cur = parent
                if parent.tag == 'DW_TAG_subprogram':
                    is_local = True
                    break

            if is_local:
                func_name = get_name(parent)
                if die.tag == 'DW_TAG_formal_parameter':
                    params[func_name].append(die)
                elif die.tag == 'DW_TAG_variable':
                    local_vars[func_name].append(die)
                else:
                    # unimplemented
                    raise NotImplemented

            else:
                global_vars.append(die)
    return funcs, params, local_vars, global_vars, type_map

def get_location(lines, string, count):
  new_lines = []
  for line in lines:
    if string in line:
      new_lines = lines[lines.index(line):]
      break
  for line in new_lines:
    if "DW_TAG" in line:
      new_lines = lines[lines.index(line):]
      return get_location(new_lines,string, count)
    elif "DW_AT_location" in line:
      offset = line.split("DW_AT_location")[1]
      if count == 0:
        return offset
      else:
        count = count -1
        new_lines = lines[lines.index(line):]
        return get_location(new_lines,string, count)

def get_offset(var_name,func_name, count):
  cmd = ["/usr/local/bin/llvm-dwarfdump","--name=%s" % func_name, "-c", fname]
  f = open("/tmp/a","w")
  proc = subprocess.Popen(cmd, stdout=f)
  proc.wait()
  f.close()
  f = open("/tmp/a","r")
  lines = f.readlines()
  string = "DW_AT_name\t(\"%s\")\n" % var_name
  off = get_location(lines, string, count)
  return off

def print_vars(funcs, params, local_vars, global_vars, type_map):
    out_str = ''
    #for var in global_vars:
        #t = fetch_type(var, type_map)
        #out_str += '%s %s; \n' % (t, get_name(var))
    #out_str += '\n'
    for func_name, vars in local_vars.items():
        varset = {}
        count = 0
        func_type = fetch_type(funcs[func_name], type_map, [])
        if func_type == "" or func_type == "*":
          func_type = "0 void%s" % func_type
        out_str += '%s %s' % (func_type,
                             func_name)

        out_str += ' (...)'
        out_str += '\n{\n'
        if func_name in params:
            for var in params[func_name]:
                name = get_name(var)
                if name in varset:
                  varset[name] = varset[name] + 1
                  count = varset[name]
                else:
                   varset[name] = 0
                   count = varset[name]
                offs = get_offset(get_name(var),func_name, count)
                if offs == None: continue
                t = fetch_type(var, type_map, [])
                if t =="":
                  continue
                elif t == "enum":
                  t = "4 enum"
                elif t.split(" ")[1] == "*" or t.split(" ")[1] == "":
                  t = "%s void%s" % (t.split(" ")[0], t.split(" ")[1])
                out_str += '  %s %s %s' % (t, get_name(var), offs)

        for var in vars:
            t = fetch_type(var, type_map, [])
            name = get_name(var)
            if name in varset:
              varset[name] = varset[name] + 1
              count = varset[name]
            else:
               varset[name] = 0
               count = varset[name]
            offs = get_offset(get_name(var),func_name,count)
            if offs == None: continue
            if t =="": continue
            elif t == "enum":
              t = "4 enum"
            elif t.split(" ")[1] == "*" or t.split(" ")[1] == "":
              t = "%s void%s" % (t.split(" ")[0], t.split(" ")[1])
            out_str += '  %s %s %s' % (t, get_name(var), offs)
        out_str += '}\n\n'
    for func_name, params in params.items():
        varset = {}
        if func_name in local_vars: continue
        func_type = fetch_type(funcs[func_name], type_map, [])
        if func_type == "" or func_type.split == "*":
          func_type = "0 void%s" % func_type
        out_str += '%s %s' % (func_type,
                             func_name)
        out_str += ' (...)'
        out_str += '\n{\n'
        for param in params:
            name = get_name(param)
            if name in varset:
              varset[name] = varset[name] + 1
              count = varset[name]
            else:
               varset[name] = 0
               count = varset[name]
            t = fetch_type(param, type_map, [])
            if t =="": continue
            elif t == "enum":
              t = "4 enum"
            elif t.split(" ")[1] == "*" or t.split(" ")[1] == "":
              t = "%s void%s" % (t.split(" ")[0], t.split(" ")[1])
            offs = get_offset(get_name(param),func_name, count)
            if offs == None: continue
            out_str += '  %s %s %s' % (t, get_name(param), offs)
        out_str += '}\n\n'
    if out_str == "":
      return
    else: print (out_str)
def decode_file_line(dwarfinfo, path):
    # DW_TAG_variable
    # DW_TAG_formal_parameter
    # DW_TAG_constant

    # - DW_AT_name
    # - DW_AT_external (False for static and local variables in C/C++)
    # - DW_AT_declaration
    # - DW_AT_location
    # - DW_AT_type
    # - DW_AT_specification (for C++ structure, class, or union)
    #       this may have nested DW_TAG_variable
    # - DW_AT_variable parameter : if parameter can be modified in the callee
    # - DW_AT_const_value
    # - DW_AT_endianity
    # - - DW_END_default
    # - - DW_END_big
    # - - DW_END little

    # DW_TAG_base_type
    # - DW_AT_name
    # - DW_AT_byte_size or DW_AT_bit_size
    #

    # Go over all the line programs in the DWARF information, looking for
    # one that describes the given address.

    ret = {}
    for CU in dwarfinfo.iter_CUs():
        #print_die(CU)
        funcs, params, local_vars, global_vars, type_map = fetch_vars(CU)
        print_vars(funcs, params, local_vars, global_vars, type_map)

        # TODO: line matching for each instructions and variables
        # TODO: check C++ class and objects

        lineprog = dwarfinfo.line_program_for_CU(CU)
        prevstate = None
        for entry in lineprog.get_entries():
            #print (entry)

            # We're interested in those entries where a new state is assigned
            if entry.state is None or entry.state.end_sequence:
                continue
            # Looking for a range of addresses in two consecutive states that
            # contain the required address.
            # if addrs is given, check address is in the given addrs
            if prevstate:# and prevstate.address in target_addrs_by_path[path]:
                try:
                    fname = lineprog['file_entry'][prevstate.file - 1].name
                except:
                    #fname = 'unknown'
                    continue

                if isinstance(fname, bytes):
                    fname = fname.decode()

                line = prevstate.line
                ret[prevstate.address] = (fname, line)

            prevstate = entry.state

    return ret


def get_file_line(fname):
    addr_to_line = {}
    with open(fname, 'rb') as f:
        elffile = ELFFile(f)
        if not elffile.has_dwarf_info():
            print ('No Dwarf Found in ', fname)

        else:
            dwarf = elffile.get_dwarf_info()
            addr_to_line = decode_file_line(dwarf, fname)
            exit()

    return addr_to_line


def debug_extract_helper(path):
    # use cache ...
    addr_to_line = {}
    addr_to_line = get_file_line(path)
    with open(debug_fname, 'wb') as f:
        pickle.dump(addr_to_line, f)

    res = []
    for addr in addr_to_line.keys():
        fname, line = addr_to_line[addr]
        if os.path.basename(fname) not in filelist:
            continue

        res.append((path_idx, addr, fname, line))

    del addr_to_line
    return res


def get_debug_info(path_indices, addrs_by_path, paths, filelist):

    return debug_info


if __name__ == '__main__':
#    op = OptionParser()
#    op.add_option("--db_name",
#                  action="store", dest="db_name",
#                  help="name of target database")
#    op.add_option("--col_prefix",
#                  action="store", dest="col_prefix",
#                  help="prefix of target collection, accepts regular expression. (ex) musl.*")
#    op.add_option("--filelist_dir",
#                  action="store", dest="filelist_dir",
#                  help="name of the filelist directory")
#
#    (opts, args) = op.parse_args()
    global fname
    fname = sys.argv[1]
    debug_extract_helper(fname)


