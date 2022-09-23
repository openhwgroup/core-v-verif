#zc directed test generator

asmFile = open("../zc_test.S", "w")
asmInputTop = open("asm_manual_top.s", "r")
asmInputFunc = open("asm_manual_func.s", "r")

asmFuncTemp = []

hFile = open("../zc_test.h", "w")
hInputTop = open("h_manual_top.h", "r")

# code lists
pushPopRlists = [ "ra", \
                  "ra, s0", \
                  "ra, s0-s1", \
                  "ra, s0-s2", \
                  "ra, s0-s3", \
                  "ra, s0-s4", \
                  "ra, s0-s5", \
                  "ra, s0-s6", \
                  "ra, s0-s7", \
                  "ra, s0-s8", \
                  "ra, s0-s9", \
                  "ra, s0-s11" \
                  ]

#randomly selected sreg values to avoid full set
sreg1List = ["s2", "s4", "s5", "s7"]
sreg2List = ["s6", "s3", "s1", "s0"]


# "Defines"
PUSH_POP_RLIST_LOW = 4

funcTags = ["interrupt_push_pop", "interrupt_popret", "interrupt_popretz", "interrupt_mvsa", "interrupt_mvas"]

#Generate push/pop test function
pushTagCount = 0
pushPopTags = []

print("\nGenerating push/pop test function")

asmFuncTemp.append(funcTags[0]+":\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  sw ra, 0(t0)\n")

for i in range(0, len(pushPopRlists)):
  print("generating case for rlist: "+str(PUSH_POP_RLIST_LOW+i))

  #case tag and branch
  asmFuncTemp.append("\n\n  pp_case_"+str(PUSH_POP_RLIST_LOW+i)+":\n")
  asmFuncTemp.append("    li t1, "+str(PUSH_POP_RLIST_LOW+i)+"\n")
  if i == len(pushPopRlists)-1:
    asmFuncTemp.append("    bne a0, t1, pp_case_end\n")
  else:
    asmFuncTemp.append("    bne a0, t1, pp_case_"+str(PUSH_POP_RLIST_LOW+i+1)+"\n")


  #Set up interrupt
  asmFuncTemp.append("    jal ra, trigger_irq\n")

  #Generate push tag

  tag = "push_"+str(pushTagCount)
  asmFuncTemp.append("  "+tag+":\n")
  #save for list generation
  pushPopTags.append(tag)

  #Generate instruction for test
  asmFuncTemp.append("    cm.push {"+pushPopRlists[i]+"}, -64\n")
  asmFuncTemp.append("    nop\n    nop\n\n")

  #Set up interrupt
  asmFuncTemp.append("    jal ra, trigger_irq\n")


  #Generate push tag

  tag = "pop_"+str(pushTagCount)
  asmFuncTemp.append("  "+tag+":\n")
  #save for list generation
  pushPopTags.append(tag)

  #Generate instruction for test
  asmFuncTemp.append("    cm.pop {"+pushPopRlists[i]+"}, 64\n")
  asmFuncTemp.append("    nop\n    nop\n")
  asmFuncTemp.append("    j pp_case_end\n\n")

  pushTagCount += 1

#End of function
asmFuncTemp.append("\n\n  pp_case_end:\n")
asmFuncTemp.append("  //return to caller\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  lw ra, 0(t0)\n")
asmFuncTemp.append("  jalr	x0, 0(ra)\n\n\n\n")

# END Generate push/pop test function


#Generate popret test function
popretTagCount = 0
popretTags = []

print("\nGenerating popret test function")

asmFuncTemp.append(funcTags[1]+":\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  sw ra, 0(t0)\n")

for i in range(0, len(pushPopRlists)):
  print("generating case for rlist: "+str(PUSH_POP_RLIST_LOW+i))

  #case tag and branch
  asmFuncTemp.append("\n\n  pr_case_"+str(PUSH_POP_RLIST_LOW+i)+":\n")
  asmFuncTemp.append("    li t1, "+str(PUSH_POP_RLIST_LOW+i)+"\n")
  if i == len(pushPopRlists)-1:
    asmFuncTemp.append("    bne a0, t1, pr_case_end\n")
  else:
    asmFuncTemp.append("    bne a0, t1, pr_case_"+str(PUSH_POP_RLIST_LOW+i+1)+"\n")



  #Generate pop tag
  tag = "popret_"+str(popretTagCount)
   #set up RA to target the next instruction
  asmFuncTemp.append("    la ra, "+tag+"_ret\n")

  #Push instruction to set stack frame
  asmFuncTemp.append("    cm.push {"+pushPopRlists[i]+"}, -64\n")

  #Set up interrupt
  asmFuncTemp.append("    jal ra, trigger_irq\n")




  asmFuncTemp.append("  "+tag+":\n")
  #save for list generation
  popretTags.append(tag)

  #Generate instruction for test
  asmFuncTemp.append("    cm.popret {"+pushPopRlists[i]+"}, 64\n")

  asmFuncTemp.append("  "+tag+"_ret:\n")
  asmFuncTemp.append("    nop\n    nop\n")
  asmFuncTemp.append("    j pr_case_end\n\n")

  popretTagCount += 1

#End of function
asmFuncTemp.append("\n\n  pr_case_end:\n")
asmFuncTemp.append("  //return to caller\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  lw ra, 0(t0)\n")
asmFuncTemp.append("  jalr	x0, 0(ra)\n")

# END Generate popret test function

#Generate popretz test function
popretzTagCount = 0
popretzTags = []

print("\nGenerating popretz test function")


asmFuncTemp.append(funcTags[2]+":\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  sw ra, 0(t0)\n")

for i in range(0, len(pushPopRlists)):
  print("generating case for rlist: "+str(PUSH_POP_RLIST_LOW+i))

  #case tag and branch
  asmFuncTemp.append("\n\n  prz_case_"+str(PUSH_POP_RLIST_LOW+i)+":\n")
  asmFuncTemp.append("    li t1, "+str(PUSH_POP_RLIST_LOW+i)+"\n")
  if i == len(pushPopRlists)-1:
    asmFuncTemp.append("    bne a0, t1, prz_case_end\n")
  else:
    asmFuncTemp.append("    bne a0, t1, prz_case_"+str(PUSH_POP_RLIST_LOW+i+1)+"\n")



  #Generate pop tag
  tag = "popretz_"+str(popretzTagCount)
   #set up RA to target the next instruction
  asmFuncTemp.append("    la ra, "+tag+"_ret\n")

  #Push instruction to set stack frame
  asmFuncTemp.append("    cm.push {"+pushPopRlists[i]+"}, -64\n")

  #Set up interrupt
  asmFuncTemp.append("    jal ra, trigger_irq\n")




  asmFuncTemp.append("  "+tag+":\n")
  #save for list generation
  popretzTags.append(tag)

  #Generate instruction for test
  asmFuncTemp.append("    cm.popretz {"+pushPopRlists[i]+"}, 64\n")

  asmFuncTemp.append("  "+tag+"_ret:\n")
  asmFuncTemp.append("    nop\n    nop\n")
  asmFuncTemp.append("    j prz_case_end\n\n")

  popretzTagCount += 1

#End of function
asmFuncTemp.append("\n\n  prz_case_end:\n")
asmFuncTemp.append("  //return to caller\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  lw ra, 0(t0)\n")
asmFuncTemp.append("  jalr	x0, 0(ra)\n")

# END Generate popretz test function


#Generate mvsa01 test function
print("\nGenerating mvsa01 test function")
mvsaTagCount = 0
mvsaTags = []

asmFuncTemp.append(funcTags[3]+":\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  sw ra, 0(t0)\n")

for s1 in sreg1List:
  for s2 in sreg2List:
    print("generating case: " +str(mvsaTagCount) + " for sregs: " + s1 + ", " + s2)


    #case tag and branch
    asmFuncTemp.append("\n\n  sa_case_"+str(mvsaTagCount)+":\n")
    asmFuncTemp.append("    li t1, "+str(mvsaTagCount)+"\n")
    if mvsaTagCount == len(sreg1List)*len(sreg2List)-1:
      asmFuncTemp.append("    bne a0, t1, sa_case_end\n")
    else:
      asmFuncTemp.append("    bne a0, t1, sa_case_"+str(mvsaTagCount+1)+"\n")

    #Populate sregs with random data
    asmFuncTemp.append("    mv " + s1 + ", a2\n")
    asmFuncTemp.append("    mv " + s2 + ", a3\n")
    #Set up interrupt
    asmFuncTemp.append("    jal ra, trigger_irq\n")

    #Generate push tag

    tag = "mvsa_"+str(mvsaTagCount)
    asmFuncTemp.append("  "+tag+":\n")
    #save for list generation
    mvsaTags.append(tag)

    #Generate instruction for test
    asmFuncTemp.append("    cm.mvsa01 "+s1+", "+s2+"\n")
    asmFuncTemp.append("    nop\n    nop\n")
    asmFuncTemp.append("    j sa_case_end\n\n")

    mvsaTagCount += 1

#End of function
asmFuncTemp.append("\n\n  sa_case_end:\n")
asmFuncTemp.append("  //return to caller\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  lw ra, 0(t0)\n")
asmFuncTemp.append("  jalr	x0, 0(ra)\n\n\n\n")

# END Generate mvsa test function

#Generate mva01s test function
print("\nGenerating mva01s test function")
mvasTagCount = 0
mvasTags = []

asmFuncTemp.append(funcTags[4]+":\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  sw ra, 0(t0)\n")

for s1 in sreg1List:
  for s2 in sreg2List:
    print("generating case: " +str(mvasTagCount) + " for sregs: " + s1 + ", " + s2)


    #case tag and branch
    asmFuncTemp.append("\n\n  as_case_"+str(mvasTagCount)+":\n")
    asmFuncTemp.append("    li t1, "+str(mvasTagCount)+"\n")
    if mvasTagCount == len(sreg1List)*len(sreg2List)-1:
      asmFuncTemp.append("    bne a0, t1, as_case_end\n")
    else:
      asmFuncTemp.append("    bne a0, t1, as_case_"+str(mvasTagCount+1)+"\n")

    #Populate sregs with random data
    asmFuncTemp.append("    mv " + s1 + ", a2\n")
    asmFuncTemp.append("    mv " + s2 + ", a3\n")
    #Set up interrupt
    asmFuncTemp.append("    jal ra, trigger_irq\n")

    #Generate push tag

    tag = "mvas_"+str(mvasTagCount)
    asmFuncTemp.append("  "+tag+":\n")
    #save for list generation
    mvasTags.append(tag)

    #Generate instruction for test
    asmFuncTemp.append("    cm.mva01s "+s1+", "+s2+"\n")
    asmFuncTemp.append("    nop\n    nop\n")
    asmFuncTemp.append("    j as_case_end\n\n")

    mvasTagCount += 1

#End of function
asmFuncTemp.append("\n\n  as_case_end:\n")
asmFuncTemp.append("  //return to caller\n")
asmFuncTemp.append("  la t0, stored_ra\n")
asmFuncTemp.append("  lw ra, 0(t0)\n")
asmFuncTemp.append("  jalr	x0, 0(ra)\n\n\n\n")

# END Generate mvas test function

#Generate asmfile
for line in asmInputTop:
  asmFile.write(line)

#Generate list of tags
asmFile.write("//Generated Functions\n")
for func in funcTags:
  asmFile.write(".global "+func+"\n")

asmFile.write("\n\n")

asmFile.write("//instruction tags\n")
for tag in pushPopTags:
  asmFile.write(".global "+tag+"\n")
for tag in popretTags:
  asmFile.write(".global "+tag+"\n")
for tag in popretzTags:
  asmFile.write(".global "+tag+"\n")
for tag in mvsaTags:
  asmFile.write(".global "+tag+"\n")
for tag in mvasTags:
  asmFile.write(".global "+tag+"\n")

#discard header in functions file
for line in asmInputFunc:
  if "_GEN END OF HEADER GEN_" in line:
    break

for line in asmInputFunc:
  asmFile.write(line)

asmFile.write("\n\n")
asmFile.write("//Generated Functions\n")
for line in asmFuncTemp:
  asmFile.write(line)


#Generate H file:
for line in hInputTop:
  hFile.write(line)


hFile.write("//Generated test functions\n")
hFile.write("//functions time interrupts to hit atomic part of named instruction type\n")
for func in funcTags:
  if (func == "interrupt_mvsa") or (func == "interrupt_mvas"):
    hFile.write("extern volatile void "+func+"(uint32_t, uint32_t, uint32_t);\n")
  else:
    hFile.write("extern volatile void "+func+"(uint32_t);\n")
#pushpop
hFile.write("\n\n//Generated list of push/pop instr addresses\n")
hFile.write("#define PUSHPOP_INSTR_SIZE " + str(len(pushPopTags)) + "\n\n")
for tag in pushPopTags:
  hFile.write("extern uint32_t " + tag + ";\n")

hFile.write("\nuint32_t pushpop_instr_list[PUSHPOP_INSTR_SIZE] = {\n")
for tag in pushPopTags:
  if tag == pushPopTags[len(pushPopTags)-1]:
    hFile.write("    (uint32_t)&" + tag + "\n")
  else:
    hFile.write("    (uint32_t)&" + tag + ",\n")
hFile.write("};\n")

#popret
hFile.write("//Generated list of popret instr addresses\n")
hFile.write("#define POPRET_INSTR_SIZE " + str(len(popretTags)) + "\n\n")
for tag in popretTags:
  hFile.write("extern uint32_t " + tag + ";\n")

hFile.write("\nuint32_t popret_instr_list[POPRET_INSTR_SIZE] = {\n")
for tag in popretTags:
  if tag == popretTags[len(popretTags)-1]:
    hFile.write("    (uint32_t)&" + tag + "\n")
  else:
    hFile.write("    (uint32_t)&" + tag + ",\n")
hFile.write("};\n")

#popretz
hFile.write("//Generated list of popretz instr addresses\n")
hFile.write("#define POPRETZ_INSTR_SIZE " + str(len(popretzTags)) + "\n\n")
for tag in popretzTags:
  hFile.write("extern uint32_t " + tag + ";\n")

hFile.write("\nuint32_t popretz_instr_list[POPRET_INSTR_SIZE] = {\n")
for tag in popretzTags:
  if tag == popretzTags[len(popretzTags)-1]:
    hFile.write("    (uint32_t)&" + tag + "\n")
  else:
    hFile.write("    (uint32_t)&" + tag + ",\n")
hFile.write("};\n")

#mvsa
hFile.write("//Generated list of mvsa instr addresses\n")
hFile.write("#define MVSA_INSTR_SIZE " + str(len(mvsaTags)) + "\n\n")
for tag in mvsaTags:
  hFile.write("extern uint32_t " + tag + ";\n")

hFile.write("\nuint32_t mvsa_instr_list[MVSA_INSTR_SIZE] = {\n")
for tag in mvsaTags:
  if tag == mvsaTags[len(mvsaTags)-1]:
    hFile.write("    (uint32_t)&" + tag + "\n")
  else:
    hFile.write("    (uint32_t)&" + tag + ",\n")
hFile.write("};\n")

#mvas
hFile.write("//Generated list of mvas instr addresses\n")
hFile.write("#define MVAS_INSTR_SIZE " + str(len(mvasTags)) + "\n\n")
for tag in mvasTags:
  hFile.write("extern uint32_t " + tag + ";\n")

hFile.write("\nuint32_t mvas_instr_list[MVAS_INSTR_SIZE] = {\n")
for tag in mvasTags:
  if tag == mvasTags[len(mvasTags)-1]:
    hFile.write("    (uint32_t)&" + tag + "\n")
  else:
    hFile.write("    (uint32_t)&" + tag + ",\n")
hFile.write("};\n")



hFile.write("#endif\n\n")

#close files
asmFile.close()
asmInputTop.close()
asmInputFunc.close()
hFile.close()
hInputTop.close()
