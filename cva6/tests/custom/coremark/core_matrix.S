    .file   "core_matrix.c"
    .option nopic
    .attribute arch, "rv32i2p0_m2p0"
    .attribute unaligned_access, 0
    .attribute stack_align, 16
    .text
    .section    .text.matrix_test,"ax",@progbits
    .align  2
    .globl  matrix_test
    .type   matrix_test, @function
matrix_test:
    addi    sp,sp,-96
    sw  s2,80(sp)
    sw  ra,92(sp)
    li  s2,-4096
    sw  s0,88(sp)
    sw  s1,84(sp)
    sw  s3,76(sp)
    sw  s4,72(sp)
    sw  s5,68(sp)
    sw  s6,64(sp)
    sw  s7,60(sp)
    sw  s8,56(sp)
    sw  s9,52(sp)
    sw  s10,48(sp)
    sw  s11,44(sp)
    sw  a2,4(sp)
    sw  a3,8(sp)
    or  s2,a4,s2
    beq a0,zero,.L2
    slli    s0,a0,1
    neg a6,a0
    slli    s3,a4,16
    add a2,a2,s0
    mv  a7,a4
    mv  t6,a0
    mv  s7,a1
    slli    a0,a6,1
    srli    s3,s3,16
    mv  a4,a2
    li  a1,0
    slli    a6,a6,2
.L3:
    add t1,a4,a0
    sub a3,a4,t1
    addi    ra,a3,-2
    srli    t0,ra,1
    addi    t2,t0,1
    andi    s1,t2,7
    mv  a5,t1
    beq s1,zero,.L4
    li  s4,1
    beq s1,s4,.L262
    li  s5,2
    beq s1,s5,.L263
    li  s6,3
    beq s1,s6,.L264
    li  s8,4
    beq s1,s8,.L265
    li  s9,5
    beq s1,s9,.L266
    li  s10,6
    beq s1,s10,.L267
    lhu s11,0(t1)
    addi    a5,t1,2
    add t4,s3,s11
    sh  t4,0(t1)
.L267:
    lhu t5,0(a5)
    addi    a5,a5,2
    add t3,s3,t5
    sh  t3,-2(a5)
.L266:
    lhu a3,0(a5)
    addi    a5,a5,2
    add ra,s3,a3
    sh  ra,-2(a5)
.L265:
    lhu t0,0(a5)
    addi    a5,a5,2
    add t2,s3,t0
    sh  t2,-2(a5)
.L264:
    lhu s1,0(a5)
    addi    a5,a5,2
    add s4,s3,s1
    sh  s4,-2(a5)
.L263:
    lhu s5,0(a5)
    addi    a5,a5,2
    add s6,s3,s5
    sh  s6,-2(a5)
.L262:
    lhu s8,0(a5)
    addi    a5,a5,2
    add s9,s3,s8
    sh  s9,-2(a5)
    beq a5,a4,.L410
.L4:
    lhu s10,0(a5)
    lhu s11,2(a5)
    lhu t2,4(a5)
    lhu t0,6(a5)
    lhu t5,8(a5)
    lhu t4,10(a5)
    lhu t3,12(a5)
    lhu a3,14(a5)
    add s1,s3,s10
    add ra,s3,s11
    add s4,s3,t2
    add s5,s3,t0
    add s6,s3,t5
    add s8,s3,t4
    add s9,s3,t3
    add s10,s3,a3
    sh  s1,0(a5)
    sh  ra,2(a5)
    sh  s4,4(a5)
    sh  s5,6(a5)
    sh  s6,8(a5)
    sh  s8,10(a5)
    sh  s9,12(a5)
    sh  s10,14(a5)
    addi    a5,a5,16
    bne a5,a4,.L4
.L410:
    addi    s1,a1,1
    sub a4,t1,a6
    beq t6,s1,.L5
    mv  a1,s1
    j   .L3
.L5:
    li  t4,0
    li  t5,0
.L7:
    add t1,a0,a2
    sub a5,a2,t1
    addi    t6,a5,-2
    srli    s11,t6,1
    addi    t2,s11,1
    slli    t0,t4,2
    andi    a3,t2,7
    add a5,t0,s7
    mv  a4,t1
    beq a3,zero,.L6
    li  t3,1
    beq a3,t3,.L268
    li  ra,2
    beq a3,ra,.L269
    li  s4,3
    beq a3,s4,.L270
    li  s5,4
    beq a3,s5,.L271
    li  s6,5
    beq a3,s6,.L272
    li  s8,6
    beq a3,s8,.L273
    lh  s9,0(t1)
    addi    a4,t1,2
    addi    a5,a5,4
    mul s10,s9,a7
    sw  s10,-4(a5)
.L273:
    lh  t6,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul s11,t6,a7
    sw  s11,-4(a5)
.L272:
    lh  t2,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul t0,t2,a7
    sw  t0,-4(a5)
.L271:
    lh  a3,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul t3,a3,a7
    sw  t3,-4(a5)
.L270:
    lh  ra,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul s4,ra,a7
    sw  s4,-4(a5)
.L269:
    lh  s5,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul s6,s5,a7
    sw  s6,-4(a5)
.L268:
    lh  s8,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul s9,s8,a7
    sw  s9,-4(a5)
    beq a4,a2,.L409
.L6:
    lh  s10,0(a4)
    lh  s11,2(a4)
    lh  ra,4(a4)
    lh  t2,6(a4)
    lh  t0,8(a4)
    lh  t6,10(a4)
    lh  t3,12(a4)
    lh  a3,14(a4)
    mul s5,s10,a7
    addi    a4,a4,16
    addi    a5,a5,32
    mul s4,s11,a7
    sw  s5,-32(a5)
    mul s6,ra,a7
    sw  s4,-28(a5)
    mul s8,t2,a7
    sw  s6,-24(a5)
    mul s9,t0,a7
    sw  s8,-20(a5)
    mul s10,t6,a7
    sw  s9,-16(a5)
    mul s11,t3,a7
    sw  s10,-12(a5)
    mul ra,a3,a7
    sw  s11,-8(a5)
    sw  ra,-4(a5)
    bne a4,a2,.L6
.L409:
    addi    a4,t5,1
    add t4,t4,s1
    sub a2,t1,a6
    beq t5,a1,.L418
    mv  t5,a4
    j   .L7
.L418:
    slli    t5,s1,2
    add s6,s7,t5
    neg t1,s1
    sw  t5,12(sp)
    mv  a3,s6
    li  a0,0
    li  t4,0
    li  t3,0
    li  a7,0
    slli    t1,t1,3
.L8:
    add t2,a6,a3
    sub a5,a3,t2
    addi    t0,a5,-4
    srli    t6,t0,2
    addi    s5,t6,1
    andi    s4,s5,7
    mv  a2,t2
    beq s4,zero,.L11
    li  s8,1
    beq s4,s8,.L274
    li  s9,2
    beq s4,s9,.L275
    li  s10,3
    beq s4,s10,.L276
    li  s11,4
    beq s4,s11,.L277
    li  ra,5
    beq s4,ra,.L278
    li  a4,6
    beq s4,a4,.L279
    mv  a2,t4
    lw  t4,0(t2)
    slli    a0,a0,16
    srli    t5,a0,16
    add t3,t3,t4
    ble t3,s2,.L381
    addi    t3,t5,10
    slli    s5,t3,16
    srai    a0,s5,16
    li  t3,0
.L382:
    addi    a2,t2,4
.L279:
    mv  s4,t4
    lw  t4,0(a2)
    slli    s8,a0,16
    srli    s9,s8,16
    add t3,t3,t4
    ble t3,s2,.L383
    addi    a4,s9,10
    slli    a0,a4,16
    srai    a0,a0,16
    li  t3,0
.L384:
    addi    a2,a2,4
.L278:
    mv  t5,t4
    lw  t4,0(a2)
    slli    a5,a0,16
    srli    t0,a5,16
    add t3,t3,t4
    ble t3,s2,.L385
    addi    t3,t0,10
    slli    s8,t3,16
    srai    a0,s8,16
    li  t3,0
.L386:
    addi    a2,a2,4
.L277:
    mv  s9,t4
    lw  t4,0(a2)
    slli    s10,a0,16
    srli    s11,s10,16
    add t3,t3,t4
    ble t3,s2,.L387
    addi    t5,s11,10
    slli    a5,t5,16
    srai    a0,a5,16
    li  t3,0
.L388:
    addi    a2,a2,4
.L276:
    mv  t0,t4
    lw  t4,0(a2)
    slli    t6,a0,16
    srli    s5,t6,16
    add t3,t3,t4
    ble t3,s2,.L389
    addi    t3,s5,10
    slli    s10,t3,16
    srai    a0,s10,16
    li  t3,0
.L390:
    addi    a2,a2,4
.L275:
    mv  s11,t4
    lw  t4,0(a2)
    slli    ra,a0,16
    srli    a4,ra,16
    add t3,t3,t4
    ble t3,s2,.L391
    addi    t0,a4,10
    slli    t6,t0,16
    srai    a0,t6,16
    li  t3,0
.L392:
    addi    a2,a2,4
.L274:
    mv  s5,t4
    lw  t4,0(a2)
    slli    s4,a0,16
    srli    s8,s4,16
    add t3,t3,t4
    ble t3,s2,.L393
    addi    t3,s8,10
    slli    ra,t3,16
    srai    a0,ra,16
    li  t3,0
.L394:
    addi    a2,a2,4
    bne a2,a3,.L11
.L395:
    addi    t6,a7,1
    sub a3,t2,t1
    beq a1,a7,.L419
    mv  a7,t6
    j   .L8
.L421:
    sgt t4,a4,t4
    lw  s9,4(a2)
    add a5,t5,t4
    slli    t0,a5,16
    srai    s4,t0,16
    slli    s10,s4,16
    add t3,s8,s9
    addi    a2,a2,4
    srli    s11,s10,16
    ble t3,s2,.L420
.L206:
    lw  t0,4(a2)
    addi    t4,s11,10
    slli    a5,t4,16
    srai    t5,a5,16
    li  t3,0
    slli    t6,t5,16
    add s4,t3,t0
    srli    s5,t6,16
    ble s4,s2,.L397
.L422:
    lw  a4,8(a2)
    addi    t3,s5,10
    slli    ra,t3,16
    srai    s11,ra,16
    li  s4,0
    slli    a0,s11,16
    add t6,s4,a4
    srli    t5,a0,16
    ble t6,s2,.L399
.L423:
    lw  s9,12(a2)
    addi    s4,t5,10
    slli    s8,s4,16
    srai    s5,s8,16
    li  t6,0
    slli    s10,s5,16
    add ra,t6,s9
    srli    s11,s10,16
    ble ra,s2,.L401
.L424:
    lw  t0,16(a2)
    addi    t6,s11,10
    slli    t4,t6,16
    srai    t5,t4,16
    li  ra,0
    slli    a5,t5,16
    add s4,ra,t0
    srli    s5,a5,16
    ble s4,s2,.L403
.L425:
    lw  a4,20(a2)
    addi    ra,s5,10
    slli    t3,ra,16
    srai    s11,t3,16
    li  s4,0
    slli    a0,s11,16
    add t6,s4,a4
    srli    t5,a0,16
    ble t6,s2,.L405
.L426:
    lw  t4,24(a2)
    addi    s4,t5,10
    slli    s8,s4,16
    srai    s5,s8,16
    li  t6,0
    slli    s9,s5,16
    add t3,t6,t4
    srli    s10,s9,16
    ble t3,s2,.L407
.L427:
    addi    a0,s10,10
    slli    t5,a0,16
    srai    a0,t5,16
    li  t3,0
.L408:
    addi    a2,a2,28
    beq a2,a3,.L395
.L11:
    lw  a4,0(a2)
    slli    a0,a0,16
    srli    t5,a0,16
    add s8,t3,a4
    ble s8,s2,.L421
    lw  s9,4(a2)
    addi    t6,t5,10
    slli    s5,t6,16
    srai    s4,s5,16
    li  s8,0
    slli    s10,s4,16
    add t3,s8,s9
    addi    a2,a2,4
    srli    s11,s10,16
    bgt t3,s2,.L206
.L420:
    sgt ra,s9,a4
    lw  t0,4(a2)
    add a4,s11,ra
    slli    a0,a4,16
    srai    t5,a0,16
    slli    t6,t5,16
    add s4,t3,t0
    srli    s5,t6,16
    bgt s4,s2,.L422
.L397:
    sgt s8,t0,s9
    lw  a4,8(a2)
    add s9,s5,s8
    slli    s10,s9,16
    srai    s11,s10,16
    slli    a0,s11,16
    add t6,s4,a4
    srli    t5,a0,16
    bgt t6,s2,.L423
.L399:
    sgt t4,a4,t0
    lw  s9,12(a2)
    add a5,t5,t4
    slli    t0,a5,16
    srai    s5,t0,16
    slli    s10,s5,16
    add ra,t6,s9
    srli    s11,s10,16
    bgt ra,s2,.L424
.L401:
    sgt t3,s9,a4
    lw  t0,16(a2)
    add a4,s11,t3
    slli    a0,a4,16
    srai    t5,a0,16
    slli    a5,t5,16
    add s4,ra,t0
    srli    s5,a5,16
    bgt s4,s2,.L425
.L403:
    sgt s8,t0,s9
    lw  a4,20(a2)
    add s9,s5,s8
    slli    s10,s9,16
    srai    s11,s10,16
    slli    a0,s11,16
    add t6,s4,a4
    srli    t5,a0,16
    bgt t6,s2,.L426
.L405:
    sgt t4,a4,t0
    add t0,t5,t4
    lw  t4,24(a2)
    slli    a5,t0,16
    srai    s5,a5,16
    slli    s9,s5,16
    add t3,t6,t4
    srli    s10,s9,16
    bgt t3,s2,.L427
.L407:
    sgt s11,t4,a4
    add ra,s10,s11
    slli    a4,ra,16
    srai    a0,a4,16
    j   .L408
.L393:
    sgt s9,t4,s5
    add s10,s8,s9
    slli    s11,s10,16
    srai    a0,s11,16
    j   .L394
.L391:
    sgt a0,t4,s11
    add t5,a4,a0
    slli    a5,t5,16
    srai    a0,a5,16
    j   .L392
.L389:
    sgt s4,t4,t0
    add s8,s5,s4
    slli    s9,s8,16
    srai    a0,s9,16
    j   .L390
.L387:
    sgt ra,t4,s9
    add a4,s11,ra
    slli    a0,a4,16
    srai    a0,a0,16
    j   .L388
.L385:
    sgt t6,t4,t5
    add s5,t0,t6
    slli    s4,s5,16
    srai    a0,s4,16
    j   .L386
.L383:
    sgt s10,t4,s4
    add s11,s9,s10
    slli    ra,s11,16
    srai    a0,ra,16
    j   .L384
.L419:
    li  a1,0
    call    crc16
    lw  t2,8(sp)
    lw  s11,4(sp)
    mv  a1,s7
    add t0,t2,s0
    li  t6,0
    sw  s2,16(sp)
    sw  a0,20(sp)
.L14:
    sub a5,t0,t2
    addi    s5,a5,-2
    srli    s4,s5,1
    addi    s8,s4,1
    slli    t4,t6,1
    andi    s9,s8,7
    add a3,s11,t4
    mv  a2,t2
    li  a5,0
    beq s9,zero,.L13
    li  s10,1
    beq s9,s10,.L280
    li  t3,2
    beq s9,t3,.L281
    li  ra,3
    beq s9,ra,.L282
    li  a4,4
    beq s9,a4,.L283
    li  a0,5
    beq s9,a0,.L284
    li  t5,6
    beq s9,t5,.L285
    lh  t1,0(a3)
    lh  a6,0(t2)
    addi    a3,a3,2
    addi    a2,t2,2
    mul a5,t1,a6
.L285:
    lh  s2,0(a3)
    lh  a7,0(a2)
    addi    a3,a3,2
    addi    a2,a2,2
    mul s5,s2,a7
    add a5,a5,s5
.L284:
    lh  s4,0(a3)
    lh  s8,0(a2)
    addi    a3,a3,2
    addi    a2,a2,2
    mul t4,s4,s8
    add a5,a5,t4
.L283:
    lh  s9,0(a3)
    lh  s10,0(a2)
    addi    a3,a3,2
    addi    a2,a2,2
    mul t3,s9,s10
    add a5,a5,t3
.L282:
    lh  ra,0(a3)
    lh  a4,0(a2)
    addi    a3,a3,2
    addi    a2,a2,2
    mul a0,ra,a4
    add a5,a5,a0
.L281:
    lh  t5,0(a3)
    lh  t1,0(a2)
    addi    a3,a3,2
    addi    a2,a2,2
    mul a6,t5,t1
    add a5,a5,a6
.L280:
    lh  s2,0(a3)
    lh  a7,0(a2)
    addi    a2,a2,2
    addi    a3,a3,2
    mul s5,s2,a7
    add a5,a5,s5
    beq t0,a2,.L380
.L13:
    lh  s4,0(a3)
    lh  t3,0(a2)
    lh  s5,2(a2)
    lh  s10,2(a3)
    mul a4,s4,t3
    lh  ra,4(a3)
    lh  s9,4(a2)
    lh  t4,6(a3)
    lh  s8,6(a2)
    lh  t1,8(a3)
    lh  s4,8(a2)
    lh  a7,10(a3)
    lh  s2,10(a2)
    lh  a6,12(a3)
    mul s10,s10,s5
    lh  t5,12(a2)
    lh  a0,14(a3)
    lh  t3,14(a2)
    add a5,a5,a4
    addi    a2,a2,16
    addi    a3,a3,16
    mul s5,ra,s9
    add ra,a5,s10
    mul s9,t4,s8
    add t4,ra,s5
    mul s8,t1,s4
    add t1,t4,s9
    mul a4,a7,s2
    add s4,t1,s8
    mul a7,a6,t5
    add s2,s4,a4
    mul a6,a0,t3
    add t5,s2,a7
    add a5,t5,a6
    bne t0,a2,.L13
.L380:
    sw  a5,0(a1)
    addi    a1,a1,4
    add t6,t6,s1
    bne a1,s6,.L14
    lw  s2,16(sp)
    lw  s11,20(sp)
    li  a3,0
    li  a0,0
    li  a7,0
    li  a4,0
    li  a2,0
.L18:
    slli    s6,a3,2
    add t2,s7,s6
    mv  t0,a7
    lw  a7,0(t2)
    addi    a1,s1,-1
    slli    a0,a0,16
    add a4,a4,a7
    andi    t6,a1,3
    srli    t3,a0,16
    ble a4,s2,.L428
    addi    ra,t3,10
    slli    s9,ra,16
    srai    a0,s9,16
    li  a4,0
.L367:
    li  a6,1
    addi    a1,t2,4
    bleu    s1,a6,.L368
    beq t6,zero,.L17
    beq t6,a6,.L310
    li  t4,2
    beq t6,t4,.L311
    mv  s8,a7
    lw  a7,4(t2)
    slli    t1,a0,16
    srli    s4,t1,16
    add a4,a4,a7
    ble a4,s2,.L369
    addi    a4,s4,10
    slli    t0,a4,16
    srai    a0,t0,16
    li  a4,0
.L370:
    addi    a6,a6,1
    addi    a1,a1,4
.L311:
    mv  t6,a7
    lw  a7,0(a1)
    slli    a0,a0,16
    srli    t3,a0,16
    add a4,a4,a7
    ble a4,s2,.L371
    addi    ra,t3,10
    slli    s9,ra,16
    srai    a0,s9,16
    li  a4,0
.L372:
    addi    a6,a6,1
    addi    a1,a1,4
.L310:
    mv  t4,a7
    lw  a7,0(a1)
    slli    s8,a0,16
    srli    t1,s8,16
    add a4,a4,a7
    ble a4,s2,.L373
    addi    t2,t1,10
    slli    a4,t2,16
    srai    a0,a4,16
    li  a4,0
.L374:
    addi    a6,a6,1
    addi    a1,a1,4
    bgtu    s1,a6,.L17
    j   .L368
.L430:
    sgt a7,t0,a7
    lw  t4,4(a1)
    add t3,a0,a7
    slli    s10,t3,16
    srai    ra,s10,16
    slli    t1,ra,16
    add s8,s9,t4
    addi    a6,a6,1
    addi    a1,a1,4
    srli    s4,t1,16
    ble s8,s2,.L429
.L158:
    lw  a0,4(a1)
    addi    t0,s4,10
    slli    t6,t0,16
    srai    a4,t6,16
    li  s8,0
    slli    a7,a4,16
    add s10,s8,a0
    srli    t3,a7,16
    ble s10,s2,.L376
.L431:
    lw  a7,8(a1)
    addi    t4,t3,10
    slli    s8,t4,16
    srai    s9,s8,16
    li  s10,0
    slli    t1,s9,16
    add a4,s10,a7
    srli    s4,t1,16
    ble a4,s2,.L378
.L432:
    addi    t0,s4,10
    slli    t6,t0,16
    addi    a6,a6,3
    srai    a0,t6,16
    li  a4,0
    addi    a1,a1,12
    bleu    s1,a6,.L368
.L17:
    lw  t0,0(a1)
    slli    t6,a0,16
    srli    a0,t6,16
    add s9,a4,t0
    ble s9,s2,.L430
    lw  t4,4(a1)
    addi    a5,a0,10
    slli    s5,a5,16
    srai    ra,s5,16
    li  s9,0
    slli    t1,ra,16
    add s8,s9,t4
    addi    a6,a6,1
    addi    a1,a1,4
    srli    s4,t1,16
    bgt s8,s2,.L158
.L429:
    sgt t5,t4,t0
    lw  a0,4(a1)
    add s6,s4,t5
    slli    t2,s6,16
    srai    a4,t2,16
    slli    a7,a4,16
    add s10,s8,a0
    srli    t3,a7,16
    bgt s10,s2,.L431
.L376:
    sgt a5,a0,t4
    lw  a7,8(a1)
    add s5,t3,a5
    slli    ra,s5,16
    srai    s9,ra,16
    slli    t1,s9,16
    add a4,s10,a7
    srli    s4,t1,16
    bgt a4,s2,.L432
.L378:
    sgt t5,a7,a0
    add s6,s4,t5
    slli    t2,s6,16
    addi    a6,a6,3
    srai    a0,t2,16
    addi    a1,a1,12
    bgtu    s1,a6,.L17
.L368:
    addi    a2,a2,1
    add a3,a3,s1
    bgtu    s1,a2,.L18
    mv  a1,s11
    call    crc16
    lw  t2,4(sp)
    lw  s8,12(sp)
    lw  s9,8(sp)
    sw  a0,16(sp)
    li  a0,0
    mv  s10,s7
    sw  s7,28(sp)
    sw  s2,20(sp)
    sw  s3,24(sp)
    mv  s7,a0
.L38:
    mv  a1,s9
    mv  t0,s10
    li  t6,0
.L21:
    lh  s3,0(t2)
    lh  t3,0(a1)
    addi    s5,s1,-1
    li  a0,1
    mul a5,s3,t3
    andi    ra,s5,7
    addi    a3,t2,2
    add a2,a1,s0
    bleu    s1,a0,.L331
    beq ra,zero,.L20
    beq ra,a0,.L303
    li  t4,2
    beq ra,t4,.L304
    li  a7,3
    beq ra,a7,.L305
    li  t1,4
    beq ra,t1,.L306
    li  s4,5
    beq ra,s4,.L307
    li  a4,6
    beq ra,a4,.L308
    lh  t5,0(a3)
    lh  s6,0(a2)
    li  a0,2
    addi    a3,t2,4
    mul a6,t5,s6
    add a2,a2,s0
    add a5,a5,a6
.L308:
    lh  s2,0(a3)
    lh  s11,0(a2)
    addi    a0,a0,1
    addi    a3,a3,2
    mul s3,s2,s11
    add a2,a2,s0
    add a5,a5,s3
.L307:
    lh  t3,0(a3)
    lh  s5,0(a2)
    addi    a0,a0,1
    addi    a3,a3,2
    mul ra,t3,s5
    add a2,a2,s0
    add a5,a5,ra
.L306:
    lh  t4,0(a3)
    lh  a7,0(a2)
    addi    a0,a0,1
    addi    a3,a3,2
    mul t1,t4,a7
    add a2,a2,s0
    add a5,a5,t1
.L305:
    lh  s4,0(a3)
    lh  a4,0(a2)
    addi    a0,a0,1
    addi    a3,a3,2
    mul t5,s4,a4
    add a2,a2,s0
    add a5,a5,t5
.L304:
    lh  s6,0(a3)
    lh  a6,0(a2)
    addi    a0,a0,1
    addi    a3,a3,2
    mul s2,s6,a6
    add a2,a2,s0
    add a5,a5,s2
.L303:
    lh  s11,0(a3)
    lh  s3,0(a2)
    addi    a0,a0,1
    addi    a3,a3,2
    mul t3,s11,s3
    add a2,a2,s0
    add a5,a5,t3
    bleu    s1,a0,.L331
.L20:
    add s5,a2,s0
    lh  a7,0(a3)
    lh  t1,0(a2)
    add ra,s5,s0
    lh  t5,2(a3)
    lh  t4,0(s5)
    add s4,ra,s0
    mul a4,a7,t1
    add s6,s4,s0
    lh  s5,0(s4)
    add s2,s6,s0
    lh  s4,0(s6)
    lh  s11,0(ra)
    lh  s3,4(a3)
    lh  ra,6(a3)
    lh  t3,8(a3)
    add a6,s2,s0
    mul s6,t5,t4
    lh  t1,10(a3)
    lh  s2,0(s2)
    lh  a7,12(a3)
    lh  t5,0(a6)
    add a2,a6,s0
    lh  t4,0(a2)
    lh  a6,14(a3)
    add a5,a5,a4
    addi    a0,a0,8
    mul s3,s3,s11
    add s11,a5,s6
    addi    a3,a3,16
    add a2,a2,s0
    mul ra,ra,s5
    add a4,s11,s3
    mul s5,t3,s4
    add t3,a4,ra
    mul s4,t1,s2
    add t1,t3,s5
    mul s2,a7,t5
    add a7,t1,s4
    mul s6,a6,t4
    add t5,a7,s2
    add a5,t5,s6
    bgtu    s1,a0,.L20
.L331:
    sw  a5,0(t0)
    addi    t6,t6,1
    addi    t0,t0,4
    addi    a1,a1,2
    bgtu    s1,t6,.L21
    addi    s7,s7,1
    add t2,t2,s0
    add s10,s10,s8
    bgtu    s1,s7,.L38
    lw  s2,20(sp)
    lw  s3,24(sp)
    lw  s7,28(sp)
    li  a3,0
    li  a7,0
    li  t3,0
    li  a4,0
    li  a2,0
.L22:
    slli    s10,a3,2
    add t2,s7,s10
    mv  s8,t3
    lw  t3,0(t2)
    addi    s9,s1,-1
    slli    a1,a7,16
    add a4,a4,t3
    andi    t0,s9,3
    srli    t6,a1,16
    ble a4,s2,.L433
    addi    a5,t6,10
    slli    s11,a5,16
    srai    a7,s11,16
    li  a4,0
.L354:
    li  a0,1
    addi    a1,t2,4
    bleu    s1,a0,.L355
    beq t0,zero,.L25
    beq t0,a0,.L301
    li  ra,2
    beq t0,ra,.L302
    mv  s5,t3
    lw  t3,4(t2)
    slli    s4,a7,16
    srli    t1,s4,16
    add a4,a4,t3
    ble a4,s2,.L356
    addi    a4,t1,10
    slli    s10,a4,16
    srai    a7,s10,16
    li  a4,0
.L357:
    addi    a0,a0,1
    addi    a1,a1,4
.L302:
    mv  t2,t3
    lw  t3,0(a1)
    slli    s8,a7,16
    srli    s9,s8,16
    add a4,a4,t3
    ble a4,s2,.L358
    addi    t4,s9,10
    slli    a5,t4,16
    srai    a7,a5,16
    li  a4,0
.L359:
    addi    a0,a0,1
    addi    a1,a1,4
.L301:
    mv  s11,t3
    lw  t3,0(a1)
    slli    ra,a7,16
    srli    s5,ra,16
    add a4,a4,t3
    ble a4,s2,.L360
    addi    s6,s5,10
    slli    t5,s6,16
    srai    a7,t5,16
    li  a4,0
.L361:
    addi    a0,a0,1
    addi    a1,a1,4
    bgtu    s1,a0,.L25
    j   .L355
.L435:
    sgt t3,s10,t3
    lw  s11,4(a1)
    add s9,s8,t3
    slli    t0,s9,16
    srai    a6,t0,16
    slli    a5,a6,16
    add ra,t4,s11
    addi    a0,a0,1
    addi    a1,a1,4
    srli    s5,a5,16
    ble ra,s2,.L434
.L119:
    lw  t2,4(a1)
    addi    t5,s5,10
    slli    s10,t5,16
    srai    s6,s10,16
    li  ra,0
    slli    s8,s6,16
    add s9,ra,t2
    srli    t3,s8,16
    ble s9,s2,.L363
.L436:
    addi    t4,t3,10
    lw  t3,8(a1)
    slli    s11,t4,16
    srai    a6,s11,16
    li  s9,0
    slli    ra,a6,16
    add a4,s9,t3
    srli    a5,ra,16
    ble a4,s2,.L365
.L437:
    addi    s6,a5,10
    slli    t5,s6,16
    addi    a0,a0,3
    srai    a7,t5,16
    li  a4,0
    addi    a1,a1,12
    bleu    s1,a0,.L355
.L25:
    lw  s10,0(a1)
    slli    t2,a7,16
    srli    s8,t2,16
    add t4,a4,s10
    ble t4,s2,.L435
    lw  s11,4(a1)
    addi    a4,s8,10
    slli    t6,a4,16
    srai    a6,t6,16
    li  t4,0
    slli    a5,a6,16
    add ra,t4,s11
    addi    a0,a0,1
    addi    a1,a1,4
    srli    s5,a5,16
    bgt ra,s2,.L119
.L434:
    sgt s4,s11,s10
    lw  t2,4(a1)
    add t1,s5,s4
    slli    a7,t1,16
    srai    s6,a7,16
    slli    s8,s6,16
    add s9,ra,t2
    srli    t3,s8,16
    bgt s9,s2,.L436
.L363:
    sgt t0,t2,s11
    add a4,t3,t0
    lw  t3,8(a1)
    slli    t6,a4,16
    srai    a6,t6,16
    slli    ra,a6,16
    add a4,s9,t3
    srli    a5,ra,16
    bgt a4,s2,.L437
.L365:
    sgt s5,t3,t2
    add s4,a5,s5
    slli    t1,s4,16
    addi    a0,a0,3
    srai    a7,t1,16
    addi    a1,a1,12
    bgtu    s1,a0,.L25
.L355:
    addi    a2,a2,1
    add a3,a3,s1
    bgtu    s1,a2,.L22
    lw  a1,16(sp)
    mv  a0,a7
    mv  s10,s7
    call    crc16
    lw  t0,4(sp)
    lw  t4,12(sp)
    lw  t2,8(sp)
    mv  a1,a0
    li  t6,0
.L37:
    mv  s11,t2
    mv  t3,s10
    li  t1,0
.L28:
    lh  s8,0(t0)
    lh  s9,0(s11)
    addi    ra,s1,-1
    li  a6,1
    mul a4,s8,s9
    andi    s5,ra,3
    addi    a0,t0,2
    add a2,s11,s0
    srai    s4,a4,5
    srai    a5,a4,2
    andi    a7,a5,15
    andi    s6,s4,127
    mul s4,a7,s6
    bleu    s1,a6,.L335
    beq s5,zero,.L27
    beq s5,a6,.L298
    li  t5,2
    beq s5,t5,.L299
    lh  a3,0(a0)
    lh  s8,0(a2)
    li  a6,2
    addi    a0,t0,4
    mul s9,a3,s8
    add a2,a2,s0
    srai    ra,s9,2
    srai    s5,s9,5
    andi    a4,ra,15
    andi    a5,s5,127
    mul a7,a4,a5
    add s4,s4,a7
.L299:
    lh  s6,0(a0)
    lh  t5,0(a2)
    addi    a6,a6,1
    addi    a0,a0,2
    mul a3,s6,t5
    add a2,a2,s0
    srai    s8,a3,2
    srai    s9,a3,5
    andi    ra,s8,15
    andi    s5,s9,127
    mul a4,ra,s5
    add s4,s4,a4
.L298:
    lh  a5,0(a0)
    lh  a7,0(a2)
    addi    a6,a6,1
    addi    a0,a0,2
    mul s6,a5,a7
    add a2,a2,s0
    srai    t5,s6,2
    srai    a3,s6,5
    andi    s8,t5,15
    andi    s9,a3,127
    mul ra,s8,s9
    add s4,s4,ra
    bleu    s1,a6,.L335
.L27:
    add a7,a2,s0
    lh  t5,0(a0)
    lh  s5,0(a2)
    add a5,a7,s0
    lh  a4,2(a0)
    lh  s8,0(a7)
    lh  s6,4(a0)
    add a2,a5,s0
    lh  ra,0(a5)
    mul a3,t5,s5
    lh  a7,0(a2)
    lh  s9,6(a0)
    addi    a6,a6,4
    addi    a0,a0,8
    add a2,a2,s0
    mul t5,a4,s8
    srai    s5,a3,2
    srai    a4,a3,5
    andi    s8,s5,15
    andi    a5,a4,127
    mul ra,s6,ra
    srai    a3,t5,5
    srai    s6,t5,2
    andi    a4,a3,127
    andi    t5,s6,15
    mul s9,s9,a7
    srai    a7,ra,2
    srai    ra,ra,5
    andi    s5,a7,15
    andi    s6,ra,127
    mul a5,s8,a5
    srai    a3,s9,5
    srai    s8,s9,2
    andi    s9,s8,15
    andi    a7,a3,127
    mul t5,t5,a4
    add s4,s4,a5
    mul a4,s5,s6
    add ra,s4,t5
    mul s5,s9,a7
    add s6,ra,a4
    add s4,s6,s5
    bgtu    s1,a6,.L27
.L335:
    sw  s4,0(t3)
    addi    t1,t1,1
    addi    t3,t3,4
    addi    s11,s11,2
    bgtu    s1,t1,.L28
    addi    t6,t6,1
    add t0,t0,s0
    add s10,s10,t4
    bgtu    s1,t6,.L37
    li  a4,0
    li  a0,0
    li  a6,0
    li  a2,0
    li  a3,0
.L29:
    slli    s0,a4,2
    add s10,s7,s0
    mv  t0,a6
    lw  a6,0(s10)
    addi    t6,s1,-1
    slli    t4,a0,16
    add a2,a2,a6
    andi    t2,t6,3
    srli    s11,t4,16
    bge s2,a2,.L438
    addi    a2,s11,10
    slli    a5,a2,16
    srai    a0,a5,16
    li  a2,0
.L341:
    li  t1,1
    addi    a7,s10,4
    bleu    s1,t1,.L342
    beq t2,zero,.L32
    beq t2,t1,.L296
    li  s8,2
    beq t2,s8,.L297
    mv  s9,a6
    lw  a6,4(s10)
    slli    t5,a0,16
    srli    s4,t5,16
    add a2,a2,a6
    bge s2,a2,.L343
    addi    s0,s4,10
    slli    s10,s0,16
    srai    a0,s10,16
    li  a2,0
.L344:
    addi    t1,t1,1
    addi    a7,a7,4
.L297:
    mv  t0,a6
    lw  a6,0(a7)
    slli    t6,a0,16
    srli    t2,t6,16
    add a2,a2,a6
    bge s2,a2,.L345
    addi    a0,t2,10
    slli    a2,a0,16
    srai    a0,a2,16
    li  a2,0
.L346:
    addi    t1,t1,1
    addi    a7,a7,4
.L296:
    mv  a5,a6
    lw  a6,0(a7)
    slli    s8,a0,16
    srli    s9,s8,16
    add a2,a2,a6
    bge s2,a2,.L347
    addi    s5,s9,10
    slli    s6,s5,16
    srai    a0,s6,16
    li  a2,0
.L348:
    addi    t1,t1,1
    addi    a7,a7,4
    bgtu    s1,t1,.L32
    j   .L342
.L440:
    sgt a6,s0,a6
    lw  s8,4(a7)
    add t6,t0,a6
    slli    t2,t6,16
    srai    t3,t2,16
    slli    a5,t3,16
    add a2,a0,s8
    addi    t1,t1,1
    addi    a7,a7,4
    srli    s9,a5,16
    bge s2,a2,.L439
.L92:
    lw  s10,4(a7)
    addi    s6,s9,10
    slli    s0,s6,16
    srai    s5,s0,16
    li  a2,0
    slli    t0,s5,16
    add t2,a2,s10
    srli    t6,t0,16
    bge s2,t2,.L350
.L441:
    addi    a0,t6,10
    lw  a6,8(a7)
    slli    s8,a0,16
    srai    t3,s8,16
    slli    a2,t3,16
    li  t2,0
    srli    a5,a2,16
    add a2,t2,a6
    bge s2,a2,.L352
.L442:
    addi    ra,a5,10
    slli    s5,ra,16
    addi    t1,t1,3
    srai    a0,s5,16
    li  a2,0
    addi    a7,a7,12
    bleu    s1,t1,.L342
.L32:
    lw  s0,0(a7)
    slli    s10,a0,16
    srli    t0,s10,16
    add a0,a2,s0
    bge s2,a0,.L440
    lw  s8,4(a7)
    addi    t4,t0,10
    slli    s11,t4,16
    srai    t3,s11,16
    li  a0,0
    slli    a5,t3,16
    add a2,a0,s8
    addi    t1,t1,1
    addi    a7,a7,4
    srli    s9,a5,16
    blt s2,a2,.L92
.L439:
    sgt t5,s8,s0
    lw  s10,4(a7)
    add s4,s9,t5
    slli    ra,s4,16
    srai    s5,ra,16
    slli    t0,s5,16
    add t2,a2,s10
    srli    t6,t0,16
    blt s2,t2,.L441
.L350:
    sgt a6,s10,s8
    add t4,t6,a6
    slli    s11,t4,16
    lw  a6,8(a7)
    srai    t3,s11,16
    slli    a2,t3,16
    srli    a5,a2,16
    add a2,t2,a6
    blt s2,a2,.L442
.L352:
    sgt s9,a6,s10
    add t5,a5,s9
    slli    s4,t5,16
    addi    t1,t1,3
    srai    a0,s4,16
    addi    a7,a7,12
    bgtu    s1,t1,.L32
.L342:
    addi    a3,a3,1
    add a4,a4,s1
    bgtu    s1,a3,.L29
    call    crc16
    lw  s6,4(sp)
    mv  t3,a0
    li  s2,0
    li  s7,0
.L36:
    slli    a1,s2,1
    add s0,s6,a1
    lhu s10,0(s0)
    addi    t0,s1,-1
    li  a4,1
    sub t6,s10,s3
    sh  t6,0(s0)
    andi    t2,t0,7
    addi    a5,s0,2
    bgeu    a4,s1,.L339
    beq t2,zero,.L34
    beq t2,a4,.L289
    li  t4,2
    beq t2,t4,.L290
    li  s11,3
    beq t2,s11,.L291
    li  a0,4
    beq t2,a0,.L292
    li  s8,5
    beq t2,s8,.L293
    li  a6,6
    beq t2,a6,.L294
    lhu a2,2(s0)
    li  a4,2
    addi    a5,s0,4
    sub s9,a2,s3
    sh  s9,2(s0)
.L294:
    lhu t5,0(a5)
    addi    a4,a4,1
    addi    a5,a5,2
    sub s4,t5,s3
    sh  s4,-2(a5)
.L293:
    lhu ra,0(a5)
    addi    a4,a4,1
    addi    a5,a5,2
    sub s5,ra,s3
    sh  s5,-2(a5)
.L292:
    lhu t1,0(a5)
    addi    a4,a4,1
    addi    a5,a5,2
    sub a7,t1,s3
    sh  a7,-2(a5)
.L291:
    lhu a3,0(a5)
    addi    a4,a4,1
    addi    a5,a5,2
    sub a1,a3,s3
    sh  a1,-2(a5)
.L290:
    lhu s0,0(a5)
    addi    a4,a4,1
    addi    a5,a5,2
    sub s10,s0,s3
    sh  s10,-2(a5)
.L289:
    lhu t0,0(a5)
    addi    a5,a5,2
    addi    a4,a4,1
    sub t6,t0,s3
    sh  t6,-2(a5)
    bgeu    a4,s1,.L339
.L34:
    lhu t2,0(a5)
    lhu t4,2(a5)
    lhu s11,4(a5)
    lhu s8,6(a5)
    lhu a0,8(a5)
    lhu s9,10(a5)
    lhu a2,12(a5)
    lhu s4,14(a5)
    sub ra,t2,s3
    sub s5,t4,s3
    sub t5,s11,s3
    sub a6,s8,s3
    sub t1,a0,s3
    sub a7,s9,s3
    sub a1,a2,s3
    sub a3,s4,s3
    sh  ra,0(a5)
    sh  s5,2(a5)
    sh  t5,4(a5)
    sh  a6,6(a5)
    sh  t1,8(a5)
    sh  a7,10(a5)
    sh  a1,12(a5)
    sh  a3,14(a5)
    addi    a4,a4,8
    addi    a5,a5,16
    bltu    a4,s1,.L34
.L339:
    addi    s7,s7,1
    add s2,s2,s1
    bltu    s7,s1,.L36
.L35:
    lw  ra,92(sp)
    lw  s0,88(sp)
    slli    s1,t3,16
    lw  s2,80(sp)
    lw  s3,76(sp)
    lw  s4,72(sp)
    lw  s5,68(sp)
    lw  s6,64(sp)
    lw  s7,60(sp)
    lw  s8,56(sp)
    lw  s9,52(sp)
    lw  s10,48(sp)
    lw  s11,44(sp)
    srai    a0,s1,16
    lw  s1,84(sp)
    addi    sp,sp,96
    jr  ra
.L433:
    sgt a0,t3,s8
    add a6,t6,a0
    slli    t4,a6,16
    srai    a7,t4,16
    j   .L354
.L438:
    sgt t3,a6,t0
    add t1,s11,t3
    slli    a0,t1,16
    srai    a0,a0,16
    j   .L341
.L428:
    sgt s10,a7,t0
    add a5,t3,s10
    slli    s5,a5,16
    srai    a0,s5,16
    j   .L367
.L360:
    sgt s4,t3,s11
    add t1,s5,s4
    slli    a7,t1,16
    srai    a7,a7,16
    j   .L361
.L347:
    sgt t5,a6,a5
    add s4,s9,t5
    slli    ra,s4,16
    srai    a0,ra,16
    j   .L348
.L373:
    sgt s4,a7,t4
    add t5,t1,s4
    slli    s6,t5,16
    srai    a0,s6,16
    j   .L374
.L371:
    sgt s10,a7,t6
    add a5,t3,s10
    slli    s5,a5,16
    srai    a0,s5,16
    j   .L372
.L345:
    sgt t4,a6,t0
    add s11,t2,t4
    slli    t3,s11,16
    srai    a0,t3,16
    j   .L346
.L358:
    sgt t0,t3,t2
    add t6,s9,t0
    slli    a6,t6,16
    srai    a7,a6,16
    j   .L359
.L343:
    sgt ra,a6,s9
    add s5,s4,ra
    slli    s6,s5,16
    srai    a0,s6,16
    j   .L344
.L356:
    sgt a7,t3,s5
    add s6,t1,a7
    slli    t5,s6,16
    srai    a7,t5,16
    j   .L357
.L369:
    sgt t5,a7,s8
    add s6,s4,t5
    slli    t2,s6,16
    srai    a0,t2,16
    j   .L370
.L381:
    sgt a5,t4,a2
    add t0,t5,a5
    slli    t6,t0,16
    srai    a0,t6,16
    j   .L382
.L2:
    li  a1,0
    call    crc16
    mv  a1,a0
    li  a0,0
    call    crc16
    mv  a1,a0
    li  a0,0
    call    crc16
    mv  a1,a0
    li  a0,0
    call    crc16
    mv  t3,a0
    j   .L35
    .size   matrix_test, .-matrix_test
    .section    .text.core_bench_matrix,"ax",@progbits
    .align  2
    .globl  core_bench_matrix
    .type   core_bench_matrix, @function
core_bench_matrix:
    addi    sp,sp,-16
    sw  s0,8(sp)
    lw  a3,8(a0)
    mv  s0,a2
    mv  a4,a1
    lw  a2,4(a0)
    lw  a1,12(a0)
    lw  a0,0(a0)
    sw  ra,12(sp)
    call    matrix_test
    mv  a1,s0
    lw  s0,8(sp)
    lw  ra,12(sp)
    addi    sp,sp,16
    tail    crc16
    .size   core_bench_matrix, .-core_bench_matrix
    .section    .text.core_init_matrix,"ax",@progbits
    .align  2
    .globl  core_init_matrix
    .type   core_init_matrix, @function
core_init_matrix:
    addi    sp,sp,-48
    sw  s2,36(sp)
    sw  s0,44(sp)
    sw  s1,40(sp)
    sw  s3,32(sp)
    sw  s4,28(sp)
    sw  s5,24(sp)
    sw  s6,20(sp)
    sw  s7,16(sp)
    sw  s8,12(sp)
    sw  s9,8(sp)
    sw  s10,4(sp)
    mv  a4,a0
    mv  s2,a3
    bne a2,zero,.L446
    li  a2,1
.L446:
    addi    a1,a1,-1
    andi    s0,a1,-4
    addi    s4,s0,4
    li  a5,0
    beq a4,zero,.L495
.L447:
    addi    t0,a5,1
    mul a3,t0,t0
    addi    a6,a5,2
    addi    t3,a5,3
    addi    t5,a5,4
    addi    t4,a5,5
    addi    a7,a5,6
    addi    t1,a5,7
    mv  a0,a5
    addi    a5,a5,8
    slli    t2,a3,3
    bleu    a4,t2,.L490
    mul s3,a6,a6
    mv  a0,t0
    slli    s6,s3,3
    bleu    a4,s6,.L490
    mul s7,t3,t3
    mv  a0,a6
    slli    s8,s7,3
    bleu    a4,s8,.L490
    mul s9,t5,t5
    mv  a0,t3
    slli    s10,s9,3
    bleu    a4,s10,.L490
    mul t6,t4,t4
    mv  a0,t5
    slli    a1,t6,3
    bleu    a4,a1,.L490
    mul s0,a7,a7
    mv  a0,t4
    slli    s5,s0,3
    bleu    a4,s5,.L490
    mul s1,t1,t1
    mv  a0,a7
    slli    t0,s1,3
    bleu    a4,t0,.L490
    mul a6,a5,a5
    mv  a0,t1
    slli    t3,a6,3
    bgtu    a4,t3,.L447
.L490:
    mul a4,a0,a0
    mv  s5,a0
    slli    s1,a4,1
    add s0,s4,s1
    beq a0,zero,.L451
.L450:
    li  t4,65536
    li  a3,0
    li  t2,0
    li  t6,1
    sub t5,s4,s0
    addi    t4,t4,-1
    addi    s3,a0,-1
.L455:
    mul a2,a2,t6
    slli    a7,t6,16
    srli    a5,a7,16
    slli    t1,a3,1
    add s6,t1,s0
    addi    s8,a0,-1
    andi    s9,s8,3
    add s7,t5,s6
    li  t3,1
    addi    a6,t6,1
    srai    s10,a2,31
    srli    t0,s10,16
    add a4,a2,t0
    and a2,a4,t4
    sub a2,a2,t0
    add a7,a5,a2
    slli    t1,a7,16
    srli    s8,t1,16
    add a5,s8,a5
    sh  s8,0(s6)
    andi    s10,a5,0xff
    sh  s10,0(s7)
    addi    a1,s6,2
    bgeu    t3,a0,.L492
    beq s9,zero,.L452
    beq s9,t3,.L480
    li  s7,2
    beq s9,s7,.L481
    mul s9,a2,a6
    slli    a6,a6,16
    srli    t0,a6,16
    add a7,t5,a1
    addi    a1,s6,4
    addi    a6,t6,2
    li  t3,2
    srai    a4,s9,31
    srli    t1,a4,16
    add a2,s9,t1
    and s8,a2,t4
    sub a2,s8,t1
    add a5,t0,a2
    slli    s10,a5,16
    srli    s7,s10,16
    add s9,s7,t0
    sh  s7,2(s6)
    andi    s6,s9,0xff
    sh  s6,0(a7)
.L481:
    mul t0,a2,a6
    slli    a7,a6,16
    srli    t1,a7,16
    add s8,t5,a1
    addi    t3,t3,1
    addi    a6,a6,1
    addi    a1,a1,2
    srai    a4,t0,31
    srli    a5,a4,16
    add a2,t0,a5
    and s10,a2,t4
    sub a2,s10,a5
    add s7,t1,a2
    slli    s9,s7,16
    srli    s6,s9,16
    add t0,s6,t1
    sh  s6,-2(a1)
    andi    a7,t0,0xff
    sh  a7,0(s8)
.L480:
    mul t1,a2,a6
    slli    s8,a6,16
    srli    a5,s8,16
    add s10,t5,a1
    addi    a1,a1,2
    addi    t3,t3,1
    addi    a6,a6,1
    srai    a4,t1,31
    srli    s7,a4,16
    add a2,t1,s7
    and s9,a2,t4
    sub a2,s9,s7
    add s6,a5,a2
    slli    t0,s6,16
    srli    a7,t0,16
    add t1,a7,a5
    sh  a7,-2(a1)
    andi    s8,t1,0xff
    sh  s8,0(s10)
    bgeu    t3,a0,.L492
.L452:
    mul a2,a2,a6
    addi    a5,a6,2
    addi    s6,a6,3
    slli    s10,a6,16
    srli    t0,s10,16
    slli    a7,a5,16
    slli    s10,s6,16
    srli    t1,a7,16
    srli    a7,s10,16
    addi    a4,a6,1
    srai    s10,a2,31
    srli    s10,s10,16
    add a2,a2,s10
    and a2,a2,t4
    sub s10,a2,s10
    slli    s7,a4,16
    mul a4,s10,a4
    add a2,t0,s10
    slli    s10,a2,16
    srli    a2,s10,16
    add t0,a2,t0
    add s9,t5,a1
    sh  a2,0(a1)
    andi    s10,t0,0xff
    sh  s10,0(s9)
    mv  s8,s9
    mv  a2,s9
    mv  t0,s9
    srai    s9,a4,31
    srli    s10,s9,16
    add a4,a4,s10
    and s9,a4,t4
    sub s10,s9,s10
    mul a5,s10,a5
    srli    s7,s7,16
    add a4,s7,s10
    slli    s9,a4,16
    srli    s10,s9,16
    add s7,s10,s7
    sh  s10,2(a1)
    andi    a4,s7,0xff
    sh  a4,2(s8)
    addi    a1,a1,8
    srai    s8,a5,31
    srli    s9,s8,16
    add a5,a5,s9
    and s10,a5,t4
    sub s7,s10,s9
    mul s6,s7,s6
    add a4,t1,s7
    slli    s8,a4,16
    srli    s9,s8,16
    add t1,s9,t1
    sh  s9,-4(a1)
    andi    a5,t1,0xff
    sh  a5,4(a2)
    addi    t3,t3,4
    addi    a6,a6,4
    srai    a2,s6,31
    srli    s10,a2,16
    add s7,s6,s10
    and s6,s7,t4
    sub a2,s6,s10
    add a4,a7,a2
    slli    s8,a4,16
    srli    s9,s8,16
    add a7,s9,a7
    sh  s9,-2(a1)
    andi    t1,a7,0xff
    sh  t1,6(t0)
    bltu    t3,a0,.L452
.L492:
    addi    t6,t6,1
    li  t3,0
    beq a0,zero,.L454
    mv  t3,s3
.L454:
    addi    t2,t2,1
    add t6,t3,t6
    add a3,a3,a0
    bltu    t2,a0,.L455
.L451:
    add s1,s0,s1
    addi    a3,s1,-1
    sw  s0,8(s2)
    andi    t2,a3,-4
    lw  s0,44(sp)
    addi    t5,t2,4
    sw  s4,4(s2)
    sw  s5,0(s2)
    sw  t5,12(s2)
    lw  s1,40(sp)
    lw  s2,36(sp)
    lw  s3,32(sp)
    lw  s4,28(sp)
    lw  s5,24(sp)
    lw  s6,20(sp)
    lw  s7,16(sp)
    lw  s8,12(sp)
    lw  s9,8(sp)
    lw  s10,4(sp)
    addi    sp,sp,48
    jr  ra
.L495:
    addi    s0,s0,6
    li  s5,-1
    li  a0,-1
    li  s1,2
    j   .L450
    .size   core_init_matrix, .-core_init_matrix
    .section    .text.matrix_sum,"ax",@progbits
    .align  2
    .globl  matrix_sum
    .type   matrix_sum, @function
matrix_sum:
    mv  a6,a0
    beq a0,zero,.L502
    neg a7,a0
    slli    a4,a0,2
    add a4,a1,a4
    slli    t1,a7,2
    li  a1,0
    li  a0,0
    li  t6,0
    li  t4,0
    slli    a7,a7,3
.L501:
    add a3,t1,a4
    sub a5,a4,a3
    addi    t0,a5,-4
    srli    t2,t0,2
    addi    t3,t2,1
    andi    a5,t3,7
    mv  t3,a3
    beq a5,zero,.L500
    li  t5,1
    beq a5,t5,.L540
    li  t0,2
    beq a5,t0,.L541
    li  t2,3
    beq a5,t2,.L542
    li  t5,4
    beq a5,t5,.L543
    li  t0,5
    beq a5,t0,.L544
    li  t2,6
    beq a5,t2,.L545
    mv  t3,t6
    lw  t6,0(a3)
    slli    a0,a0,16
    srli    t5,a0,16
    add t4,t4,t6
    bge a2,t4,.L549
    addi    t4,t5,10
    slli    t3,t4,16
    srai    a0,t3,16
    li  t4,0
.L550:
    addi    t3,a3,4
.L545:
    mv  t5,t6
    lw  t6,0(t3)
    slli    a0,a0,16
    srli    t0,a0,16
    add t4,t4,t6
    bge a2,t4,.L551
    addi    t4,t0,10
    slli    a0,t4,16
    srai    a0,a0,16
    li  t4,0
.L552:
    addi    t3,t3,4
.L544:
    mv  t0,t6
    lw  t6,0(t3)
    slli    a5,a0,16
    srli    t2,a5,16
    add t4,t4,t6
    bge a2,t4,.L553
    addi    t4,t2,10
    slli    a5,t4,16
    srai    a0,a5,16
    li  t4,0
.L554:
    addi    t3,t3,4
.L543:
    mv  t2,t6
    lw  t6,0(t3)
    slli    t5,a0,16
    srli    a0,t5,16
    add t4,t4,t6
    bge a2,t4,.L555
    addi    t4,a0,10
    slli    t5,t4,16
    srai    a0,t5,16
    li  t4,0
.L556:
    addi    t3,t3,4
.L542:
    mv  t0,t6
    lw  t6,0(t3)
    slli    a0,a0,16
    srli    t2,a0,16
    add t4,t4,t6
    bge a2,t4,.L557
    addi    t4,t2,10
    slli    a0,t4,16
    srai    a0,a0,16
    li  t4,0
.L558:
    addi    t3,t3,4
.L541:
    mv  t2,t6
    lw  t6,0(t3)
    slli    a5,a0,16
    srli    t5,a5,16
    add t4,t4,t6
    bge a2,t4,.L559
    addi    t4,t5,10
    slli    a5,t4,16
    srai    a0,a5,16
    li  t4,0
.L560:
    addi    t3,t3,4
.L540:
    mv  t5,t6
    lw  t6,0(t3)
    slli    t0,a0,16
    srli    a0,t0,16
    add t4,t4,t6
    bge a2,t4,.L561
    addi    t4,a0,10
    slli    t0,t4,16
    srai    a0,t0,16
    li  t4,0
.L562:
    addi    t3,t3,4
    bne a4,t3,.L500
.L563:
    addi    a1,a1,1
    sub a4,a3,a7
    bne a6,a1,.L501
    ret
.L578:
    slt t6,t6,t2
    add a5,t5,t6
    lw  t6,4(t3)
    slli    t0,a5,16
    srai    t5,t0,16
    slli    a5,t5,16
    add a0,t4,t6
    addi    t3,t3,4
    srli    t0,a5,16
    bge a2,a0,.L577
.L526:
    lw  t2,4(t3)
    addi    t0,t0,10
    slli    a0,t0,16
    srai    a5,a0,16
    li  a0,0
    slli    t5,a5,16
    add t4,a0,t2
    srli    a5,t5,16
    bge a2,t4,.L565
.L579:
    lw  t6,8(t3)
    addi    a5,a5,10
    slli    t4,a5,16
    srai    t5,t4,16
    li  t4,0
    slli    t0,t5,16
    add t4,t4,t6
    srli    a0,t0,16
    bge a2,t4,.L567
.L580:
    lw  t2,12(t3)
    addi    a0,a0,10
    slli    t4,a0,16
    srai    t0,t4,16
    li  t4,0
    slli    t5,t0,16
    add t0,t4,t2
    srli    a5,t5,16
    bge a2,t0,.L569
.L581:
    addi    a5,a5,10
    lw  t6,16(t3)
    slli    t0,a5,16
    srai    t5,t0,16
    li  t0,0
    slli    a0,t5,16
    add t4,t0,t6
    srli    a5,a0,16
    bge a2,t4,.L571
.L582:
    lw  t2,20(t3)
    addi    a5,a5,10
    slli    t4,a5,16
    srai    a0,t4,16
    li  t4,0
    slli    t5,a0,16
    add t4,t4,t2
    srli    t0,t5,16
    bge a2,t4,.L573
.L583:
    lw  t6,24(t3)
    addi    t0,t0,10
    slli    t4,t0,16
    srai    t5,t4,16
    li  t4,0
    slli    a0,t5,16
    add t4,t4,t6
    srli    a5,a0,16
    bge a2,t4,.L575
.L584:
    addi    a0,a5,10
    slli    a5,a0,16
    srai    a0,a5,16
    li  t4,0
.L576:
    addi    t3,t3,28
    beq a4,t3,.L563
.L500:
    lw  t2,0(t3)
    slli    a0,a0,16
    srli    t5,a0,16
    add t4,t4,t2
    bge a2,t4,.L578
    addi    t4,t5,10
    lw  t6,4(t3)
    slli    a0,t4,16
    srai    t5,a0,16
    li  t4,0
    slli    a5,t5,16
    add a0,t4,t6
    addi    t3,t3,4
    srli    t0,a5,16
    blt a2,a0,.L526
.L577:
    slt t2,t2,t6
    add t5,t0,t2
    lw  t2,4(t3)
    slli    t4,t5,16
    srai    a5,t4,16
    slli    t5,a5,16
    add t4,a0,t2
    srli    a5,t5,16
    blt a2,t4,.L579
.L565:
    slt t6,t6,t2
    add t0,a5,t6
    lw  t6,8(t3)
    slli    a0,t0,16
    srai    t5,a0,16
    slli    t0,t5,16
    add t4,t4,t6
    srli    a0,t0,16
    blt a2,t4,.L580
.L567:
    slt t2,t2,t6
    add t5,a0,t2
    lw  t2,12(t3)
    slli    a5,t5,16
    srai    t0,a5,16
    slli    t5,t0,16
    add t0,t4,t2
    srli    a5,t5,16
    blt a2,t0,.L581
.L569:
    slt t6,t6,t2
    add a0,a5,t6
    lw  t6,16(t3)
    slli    t4,a0,16
    srai    t5,t4,16
    slli    a0,t5,16
    add t4,t0,t6
    srli    a5,a0,16
    blt a2,t4,.L582
.L571:
    slt t2,t2,t6
    add t5,a5,t2
    lw  t2,20(t3)
    slli    t0,t5,16
    srai    a0,t0,16
    slli    t5,a0,16
    add t4,t4,t2
    srli    t0,t5,16
    blt a2,t4,.L583
.L573:
    slt t6,t6,t2
    add a0,t0,t6
    lw  t6,24(t3)
    slli    a5,a0,16
    srai    t5,a5,16
    slli    a0,t5,16
    add t4,t4,t6
    srli    a5,a0,16
    blt a2,t4,.L584
.L575:
    slt t2,t2,t6
    add t5,a5,t2
    slli    t0,t5,16
    srai    a0,t0,16
    j   .L576
.L561:
    slt t2,t5,t6
    add a5,a0,t2
    slli    t5,a5,16
    srai    a0,t5,16
    j   .L562
.L559:
    slt t0,t2,t6
    add a0,t5,t0
    slli    t2,a0,16
    srai    a0,t2,16
    j   .L560
.L557:
    slt a5,t0,t6
    add t5,t2,a5
    slli    t0,t5,16
    srai    a0,t0,16
    j   .L558
.L555:
    slt t0,t2,t6
    add a5,a0,t0
    slli    t2,a5,16
    srai    a0,t2,16
    j   .L556
.L553:
    slt t5,t0,t6
    add a0,t2,t5
    slli    t0,a0,16
    srai    a0,t0,16
    j   .L554
.L551:
    slt a5,t5,t6
    add t2,t0,a5
    slli    t5,t2,16
    srai    a0,t5,16
    j   .L552
.L549:
    slt a5,t3,t6
    add t0,t5,a5
    slli    t2,t0,16
    srai    a0,t2,16
    j   .L550
.L502:
    li  a0,0
    ret
    .size   matrix_sum, .-matrix_sum
    .section    .text.matrix_mul_const,"ax",@progbits
    .align  2
    .globl  matrix_mul_const
    .type   matrix_mul_const, @function
matrix_mul_const:
    beq a0,zero,.L624
    addi    sp,sp,-16
    neg t2,a0
    slli    a6,a0,1
    sw  s0,12(sp)
    sw  s1,8(sp)
    slli    s0,t2,1
    sw  s2,4(sp)
    sw  s3,0(sp)
    add a6,a2,a6
    li  t6,0
    li  t0,0
    slli    t2,t2,2
.L587:
    add a7,s0,a6
    sub a2,a6,a7
    addi    t1,a2,-2
    srli    s1,t1,1
    addi    a4,s1,1
    slli    a5,t6,2
    andi    s2,a4,7
    add a5,a1,a5
    mv  a4,a7
    beq s2,zero,.L588
    li  s3,1
    beq s2,s3,.L613
    li  t3,2
    beq s2,t3,.L614
    li  t4,3
    beq s2,t4,.L615
    li  t5,4
    beq s2,t5,.L616
    li  a2,5
    beq s2,a2,.L617
    li  t1,6
    beq s2,t1,.L618
    lh  s1,0(a7)
    addi    a4,a7,2
    addi    a5,a5,4
    mul s2,s1,a3
    sw  s2,-4(a5)
.L618:
    lh  s3,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul t3,s3,a3
    sw  t3,-4(a5)
.L617:
    lh  t4,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul t5,t4,a3
    sw  t5,-4(a5)
.L616:
    lh  a2,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul t1,a2,a3
    sw  t1,-4(a5)
.L615:
    lh  s1,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul s2,s1,a3
    sw  s2,-4(a5)
.L614:
    lh  s3,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul t3,s3,a3
    sw  t3,-4(a5)
.L613:
    lh  t4,0(a4)
    addi    a5,a5,4
    addi    a4,a4,2
    mul t5,t4,a3
    sw  t5,-4(a5)
    beq a6,a4,.L622
.L588:
    lh  s3,0(a4)
    lh  s2,2(a4)
    lh  s1,4(a4)
    lh  t5,6(a4)
    lh  t4,8(a4)
    lh  t3,10(a4)
    lh  t1,12(a4)
    lh  a2,14(a4)
    mul s3,s3,a3
    addi    a4,a4,16
    addi    a5,a5,32
    mul s2,s2,a3
    sw  s3,-32(a5)
    mul s1,s1,a3
    sw  s2,-28(a5)
    mul t5,t5,a3
    sw  s1,-24(a5)
    mul t4,t4,a3
    sw  t5,-20(a5)
    mul t3,t3,a3
    sw  t4,-16(a5)
    mul t1,t1,a3
    sw  t3,-12(a5)
    mul a2,a2,a3
    sw  t1,-8(a5)
    sw  a2,-4(a5)
    bne a6,a4,.L588
.L622:
    addi    t0,t0,1
    add t6,t6,a0
    sub a6,a7,t2
    bne a0,t0,.L587
    lw  s0,12(sp)
    lw  s1,8(sp)
    lw  s2,4(sp)
    lw  s3,0(sp)
    addi    sp,sp,16
    jr  ra
.L624:
    ret
    .size   matrix_mul_const, .-matrix_mul_const
    .section    .text.matrix_add_const,"ax",@progbits
    .align  2
    .globl  matrix_add_const
    .type   matrix_add_const, @function
matrix_add_const:
    beq a0,zero,.L666
    neg t0,a0
    slli    a3,a2,16
    slli    a5,a0,1
    slli    t2,t0,1
    srli    a3,a3,16
    add a2,a1,a5
    li  t6,0
    slli    t0,t0,2
.L667:
    add a1,t2,a2
    sub a4,a2,a1
    addi    t1,a4,-2
    srli    a6,t1,1
    addi    a7,a6,1
    andi    t3,a7,7
    mv  a5,a1
    beq t3,zero,.L684
    li  t4,1
    beq t3,t4,.L670
    li  t5,2
    beq t3,t5,.L672
    li  a4,3
    beq t3,a4,.L674
    li  t1,4
    beq t3,t1,.L676
    li  a6,5
    beq t3,a6,.L678
    li  a7,6
    beq t3,a7,.L680
    lhu t3,0(a1)
    addi    a5,a1,2
    add t4,a3,t3
    sh  t4,0(a1)
.L680:
    lhu t5,0(a5)
    addi    a5,a5,2
    add a4,a3,t5
    sh  a4,-2(a5)
.L678:
    lhu t1,0(a5)
    addi    a5,a5,2
    add a6,a3,t1
    sh  a6,-2(a5)
.L676:
    lhu a7,0(a5)
    addi    a5,a5,2
    add t3,a3,a7
    sh  t3,-2(a5)
.L674:
    lhu t4,0(a5)
    addi    a5,a5,2
    add t5,a3,t4
    sh  t5,-2(a5)
.L672:
    lhu a4,0(a5)
    addi    a5,a5,2
    add t1,a3,a4
    sh  t1,-2(a5)
.L670:
    lhu a6,0(a5)
    addi    a5,a5,2
    add a7,a3,a6
    sh  a7,-2(a5)
    beq a2,a5,.L683
.L684:
    addi    sp,sp,-16
    sw  s0,12(sp)
.L630:
    lhu s0,0(a5)
    lhu t5,2(a5)
    lhu t4,4(a5)
    lhu t3,6(a5)
    lhu t1,8(a5)
    lhu a7,10(a5)
    lhu a6,12(a5)
    lhu a4,14(a5)
    add s0,a3,s0
    add t5,a3,t5
    add t4,a3,t4
    add t3,a3,t3
    add t1,a3,t1
    add a7,a3,a7
    add a6,a3,a6
    add a4,a3,a4
    sh  s0,0(a5)
    sh  t5,2(a5)
    sh  t4,4(a5)
    sh  t3,6(a5)
    sh  t1,8(a5)
    sh  a7,10(a5)
    sh  a6,12(a5)
    sh  a4,14(a5)
    addi    a5,a5,16
    bne a2,a5,.L630
    addi    t6,t6,1
    sub a2,a1,t0
    beq a0,t6,.L627
.L686:
    add a1,t2,a2
    sub a5,a2,a1
    addi    s0,a5,-2
    srli    t5,s0,1
    addi    t4,t5,1
    andi    t3,t4,7
    mv  a5,a1
    beq t3,zero,.L630
    li  t1,1
    beq t3,t1,.L655
    li  a7,2
    beq t3,a7,.L656
    li  a6,3
    beq t3,a6,.L657
    li  a4,4
    beq t3,a4,.L658
    li  s0,5
    beq t3,s0,.L659
    li  t5,6
    bne t3,t5,.L685
.L660:
    lhu t1,0(a5)
    addi    a5,a5,2
    add a7,a3,t1
    sh  a7,-2(a5)
.L659:
    lhu a6,0(a5)
    addi    a5,a5,2
    add a4,a3,a6
    sh  a4,-2(a5)
.L658:
    lhu s0,0(a5)
    addi    a5,a5,2
    add t5,a3,s0
    sh  t5,-2(a5)
.L657:
    lhu t4,0(a5)
    addi    a5,a5,2
    add t3,a3,t4
    sh  t3,-2(a5)
.L656:
    lhu t1,0(a5)
    addi    a5,a5,2
    add a7,a3,t1
    sh  a7,-2(a5)
.L655:
    lhu a6,0(a5)
    addi    a5,a5,2
    add a4,a3,a6
    sh  a4,-2(a5)
    bne a2,a5,.L630
    addi    t6,t6,1
    sub a2,a1,t0
    bne a0,t6,.L686
.L627:
    lw  s0,12(sp)
    addi    sp,sp,16
    jr  ra
.L683:
    addi    t6,t6,1
    sub a2,a1,t0
    bne a0,t6,.L667
.L666:
    ret
.L685:
    lhu t4,0(a1)
    addi    a5,a1,2
    add t3,a3,t4
    sh  t3,0(a1)
    j   .L660
    .size   matrix_add_const, .-matrix_add_const
    .section    .text.matrix_mul_vect,"ax",@progbits
    .align  2
    .globl  matrix_mul_vect
    .type   matrix_mul_vect, @function
matrix_mul_vect:
    beq a0,zero,.L725
    addi    sp,sp,-48
    slli    t6,a0,2
    slli    t4,a0,1
    sw  s0,44(sp)
    sw  s1,40(sp)
    sw  s2,36(sp)
    sw  s3,32(sp)
    sw  s4,28(sp)
    sw  s5,24(sp)
    sw  s6,20(sp)
    sw  s7,16(sp)
    sw  s8,12(sp)
    sw  s9,8(sp)
    mv  t3,a1
    add t6,a1,t6
    add t4,a3,t4
    li  t5,0
.L690:
    sub a7,t4,a3
    addi    t0,a7,-2
    srli    t1,t0,1
    addi    t2,t1,1
    slli    a5,t5,1
    andi    s0,t2,7
    add a5,a2,a5
    mv  a4,a3
    li  t1,0
    beq s0,zero,.L689
    li  a1,1
    beq s0,a1,.L715
    li  s1,2
    beq s0,s1,.L716
    li  a6,3
    beq s0,a6,.L717
    li  s2,4
    beq s0,s2,.L718
    li  s3,5
    beq s0,s3,.L719
    li  s4,6
    beq s0,s4,.L720
    lh  s5,0(a5)
    lh  s6,0(a3)
    addi    a5,a5,2
    addi    a4,a3,2
    mul t1,s5,s6
.L720:
    lh  s7,0(a5)
    lh  s8,0(a4)
    addi    a5,a5,2
    addi    a4,a4,2
    mul s9,s7,s8
    add t1,t1,s9
.L719:
    lh  a7,0(a5)
    lh  t0,0(a4)
    addi    a5,a5,2
    addi    a4,a4,2
    mul t2,a7,t0
    add t1,t1,t2
.L718:
    lh  s0,0(a5)
    lh  a1,0(a4)
    addi    a5,a5,2
    addi    a4,a4,2
    mul s1,s0,a1
    add t1,t1,s1
.L717:
    lh  s2,0(a5)
    lh  a6,0(a4)
    addi    a5,a5,2
    addi    a4,a4,2
    mul s3,s2,a6
    add t1,t1,s3
.L716:
    lh  s4,0(a5)
    lh  s5,0(a4)
    addi    a5,a5,2
    addi    a4,a4,2
    mul s6,s4,s5
    add t1,t1,s6
.L715:
    lh  s7,0(a5)
    lh  s8,0(a4)
    addi    a4,a4,2
    addi    a5,a5,2
    mul s9,s7,s8
    add t1,t1,s9
    beq t4,a4,.L723
.L689:
    lh  t0,0(a5)
    lh  a7,0(a4)
    lh  s9,2(a4)
    lh  s5,2(a5)
    lh  a1,4(a5)
    lh  s8,4(a4)
    mul a6,t0,a7
    lh  s1,6(a5)
    lh  s7,6(a4)
    lh  s0,8(a5)
    lh  s6,8(a4)
    lh  t2,10(a5)
    lh  s4,10(a4)
    lh  t0,12(a5)
    lh  s3,12(a4)
    lh  a7,14(a5)
    mul s5,s5,s9
    lh  s2,14(a4)
    add t1,t1,a6
    addi    a4,a4,16
    addi    a5,a5,16
    mul s9,a1,s8
    add a1,t1,s5
    mul s8,s1,s7
    add s1,a1,s9
    mul s7,s0,s6
    add a6,s1,s8
    mul s0,t2,s4
    add s6,a6,s7
    mul t2,t0,s3
    add s4,s6,s0
    mul t0,a7,s2
    add s3,s4,t2
    add t1,s3,t0
    bne t4,a4,.L689
.L723:
    sw  t1,0(t3)
    addi    t3,t3,4
    add t5,t5,a0
    bne t6,t3,.L690
    lw  s0,44(sp)
    lw  s1,40(sp)
    lw  s2,36(sp)
    lw  s3,32(sp)
    lw  s4,28(sp)
    lw  s5,24(sp)
    lw  s6,20(sp)
    lw  s7,16(sp)
    lw  s8,12(sp)
    lw  s9,8(sp)
    addi    sp,sp,48
    jr  ra
.L725:
    ret
    .size   matrix_mul_vect, .-matrix_mul_vect
    .section    .text.matrix_mul_matrix,"ax",@progbits
    .align  2
    .globl  matrix_mul_matrix
    .type   matrix_mul_matrix, @function
matrix_mul_matrix:
    addi    sp,sp,-64
    sw  s0,60(sp)
    sw  s1,56(sp)
    sw  s2,52(sp)
    sw  s3,48(sp)
    sw  s4,44(sp)
    sw  s5,40(sp)
    sw  s6,36(sp)
    sw  s7,32(sp)
    sw  s8,28(sp)
    sw  s9,24(sp)
    sw  s10,20(sp)
    sw  s11,16(sp)
    sw  a1,12(sp)
    beq a0,zero,.L728
    mv  t2,a2
    slli    a2,a0,1
    mv  s7,a0
    mv  s10,a3
    add t6,t2,a2
    li  s8,0
    li  s9,0
.L730:
    lw  a5,12(sp)
    slli    t0,s8,2
    mv  t5,s10
    add t0,a5,t0
    li  s0,0
.L732:
    sub a4,t6,t2
    addi    t1,a4,-2
    srli    s1,t1,1
    addi    a0,s1,1
    andi    a6,a0,7
    mv  a1,t5
    mv  a3,t2
    li  a5,0
    beq a6,zero,.L731
    li  a7,1
    beq a6,a7,.L758
    li  s2,2
    beq a6,s2,.L759
    li  s3,3
    beq a6,s3,.L760
    li  s4,4
    beq a6,s4,.L761
    li  s5,5
    beq a6,s5,.L762
    li  s6,6
    beq a6,s6,.L763
    lh  s11,0(t2)
    lh  t3,0(t5)
    addi    a3,t2,2
    add a1,t5,a2
    mul a5,s11,t3
.L763:
    lh  t4,0(a3)
    lh  a4,0(a1)
    addi    a3,a3,2
    add a1,a1,a2
    mul t1,t4,a4
    add a5,a5,t1
.L762:
    lh  s1,0(a3)
    lh  a0,0(a1)
    addi    a3,a3,2
    add a1,a1,a2
    mul a6,s1,a0
    add a5,a5,a6
.L761:
    lh  a7,0(a3)
    lh  s2,0(a1)
    addi    a3,a3,2
    add a1,a1,a2
    mul s3,a7,s2
    add a5,a5,s3
.L760:
    lh  s4,0(a3)
    lh  s5,0(a1)
    addi    a3,a3,2
    add a1,a1,a2
    mul s6,s4,s5
    add a5,a5,s6
.L759:
    lh  s11,0(a3)
    lh  t3,0(a1)
    addi    a3,a3,2
    add a1,a1,a2
    mul t4,s11,t3
    add a5,a5,t4
.L758:
    lh  a4,0(a3)
    lh  t1,0(a1)
    addi    a3,a3,2
    add a1,a1,a2
    mul s1,a4,t1
    add a5,a5,s1
    beq t6,a3,.L767
.L731:
    add a6,a1,a2
    lh  a7,0(a3)
    lh  s2,0(a1)
    lh  t3,0(a6)
    lh  s6,2(a3)
    mul a4,a7,s2
    add a0,a6,a2
    add s4,a0,a2
    lh  s11,0(a0)
    lh  s3,4(a3)
    lh  s5,0(s4)
    add t4,s4,a2
    lh  s1,6(a3)
    add a1,t4,a2
    lh  t1,8(a3)
    mul s6,s6,t3
    lh  s4,0(t4)
    lh  a7,10(a3)
    lh  s2,0(a1)
    add a0,a1,a2
    lh  a6,12(a3)
    lh  t4,0(a0)
    add a1,a0,a2
    lh  t3,0(a1)
    lh  a0,14(a3)
    mul s3,s3,s11
    add a5,a5,a4
    add s11,a5,s6
    addi    a3,a3,16
    add a1,a1,a2
    mul s1,s1,s5
    add a4,s11,s3
    mul s5,t1,s4
    add t1,a4,s1
    mul s4,a7,s2
    add a7,t1,s5
    mul s2,a6,t4
    add a6,a7,s4
    mul s6,a0,t3
    add t4,a6,s2
    add a5,t4,s6
    bne t6,a3,.L731
.L767:
    sw  a5,0(t0)
    addi    a3,s0,1
    addi    t0,t0,4
    addi    t5,t5,2
    beq s7,a3,.L771
    mv  s0,a3
    j   .L732
.L771:
    addi    t0,s9,1
    add t2,t2,a2
    add s8,s8,s7
    add t6,t6,a2
    beq s9,s0,.L728
    mv  s9,t0
    j   .L730
.L728:
    lw  s0,60(sp)
    lw  s1,56(sp)
    lw  s2,52(sp)
    lw  s3,48(sp)
    lw  s4,44(sp)
    lw  s5,40(sp)
    lw  s6,36(sp)
    lw  s7,32(sp)
    lw  s8,28(sp)
    lw  s9,24(sp)
    lw  s10,20(sp)
    lw  s11,16(sp)
    addi    sp,sp,64
    jr  ra
    .size   matrix_mul_matrix, .-matrix_mul_matrix
    .section    .text.matrix_mul_matrix_bitextract,"ax",@progbits
    .align  2
    .globl  matrix_mul_matrix_bitextract
    .type   matrix_mul_matrix_bitextract, @function
matrix_mul_matrix_bitextract:
    beq a0,zero,.L797
    addi    sp,sp,-32
    slli    a7,a0,1
    sw  s0,28(sp)
    sw  s1,24(sp)
    sw  s2,20(sp)
    sw  s3,16(sp)
    sw  s4,12(sp)
    sw  s5,8(sp)
    sw  s6,4(sp)
    mv  t0,a0
    mv  s1,a1
    mv  s2,a3
    mv  t5,a2
    add t1,a2,a7
    li  t2,0
    li  s0,0
.L774:
    slli    t4,t2,2
    add t4,s1,t4
    mv  t3,s2
    li  t6,0
.L776:
    sub a5,t1,t5
    addi    a0,a5,-2
    srli    a1,a0,1
    addi    a2,a1,1
    andi    s4,a2,3
    mv  a6,t3
    mv  a3,t5
    li  s3,0
    beq s4,zero,.L775
    li  a4,1
    beq s4,a4,.L790
    li  s5,2
    beq s4,s5,.L791
    lh  s3,0(t5)
    lh  s6,0(t3)
    addi    a3,t5,2
    add a6,t3,a7
    mul a0,s3,s6
    srai    a5,a0,2
    srai    a1,a0,5
    andi    a2,a5,15
    andi    s4,a1,127
    mul s3,a2,s4
.L791:
    lh  s5,0(a3)
    lh  a4,0(a6)
    addi    a3,a3,2
    add a6,a6,a7
    mul s6,s5,a4
    srai    a0,s6,2
    srai    a5,s6,5
    andi    a1,a0,15
    andi    a2,a5,127
    mul s4,a1,a2
    add s3,s3,s4
.L790:
    lh  s5,0(a3)
    lh  a4,0(a6)
    addi    a3,a3,2
    add a6,a6,a7
    mul s6,s5,a4
    srai    a0,s6,2
    srai    a5,s6,5
    andi    a1,a0,15
    andi    a2,a5,127
    mul s4,a1,a2
    add s3,s3,s4
    beq t1,a3,.L795
.L775:
    add s5,a6,a7
    lh  a2,0(a6)
    lh  s4,0(a3)
    lh  a4,0(s5)
    add s6,s5,a7
    lh  a0,2(a3)
    add a6,s6,a7
    lh  a1,4(a3)
    lh  s6,0(s6)
    mul s4,s4,a2
    lh  s5,0(a6)
    lh  a2,6(a3)
    addi    a3,a3,8
    add a6,a6,a7
    mul a0,a0,a4
    srai    a5,s4,2
    srai    s4,s4,5
    andi    a4,a5,15
    andi    a5,s4,127
    mul a1,a1,s6
    srai    s6,a0,2
    srai    a0,a0,5
    andi    s4,s6,15
    andi    s6,a0,127
    mul a2,a2,s5
    srai    s5,a1,2
    srai    a1,a1,5
    andi    s5,s5,15
    andi    a1,a1,127
    mul a5,a4,a5
    srai    a0,a2,5
    srai    a4,a2,2
    andi    a4,a4,15
    andi    a2,a0,127
    mul s4,s4,s6
    add s3,s3,a5
    mul s6,s5,a1
    add s5,s3,s4
    mul a1,a4,a2
    add a5,s5,s6
    add s3,a5,a1
    bne t1,a3,.L775
.L795:
    sw  s3,0(t4)
    addi    a3,t6,1
    addi    t4,t4,4
    addi    t3,t3,2
    beq t0,a3,.L800
    mv  t6,a3
    j   .L776
.L800:
    addi    t4,s0,1
    add t5,t5,a7
    add t2,t2,t0
    add t1,t1,a7
    beq s0,t6,.L772
    mv  s0,t4
    j   .L774
.L772:
    lw  s0,28(sp)
    lw  s1,24(sp)
    lw  s2,20(sp)
    lw  s3,16(sp)
    lw  s4,12(sp)
    lw  s5,8(sp)
    lw  s6,4(sp)
    addi    sp,sp,32
    jr  ra
.L797:
    ret
    .size   matrix_mul_matrix_bitextract, .-matrix_mul_matrix_bitextract
    .ident  "GCC: (GNU) 10.2.0"
