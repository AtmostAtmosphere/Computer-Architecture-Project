.data
    n: .word 11
.text
.globl __start


jal x0, __start
#----------------------------------------------------Do not modify above text----------------------------------------------------
FUNCTION:
# Todo: Define your own function
# We store the input n in register a0, and you should store your result in register a1 
  addi sp,sp,-16
  sw x1,8(sp) #x1:instruction location
  sw a0,0(sp) #a0:input
  addi x5,a0,-10 
  bge x5,x0,L1
  addi x5,a0,-1
  bge x5,x0,L2
  addi a1,x0,7 #return 7,if x=0
  addi sp,sp,16 #pop stak
  beq x1,x0,__start #call result if finished
  jalr x0,0(x1) #return

#x6,x7:temporaries 
L1:
  #floor function
  addi x6,x0,3 
  mul a0,a0,x6
  addi x6,x6,1
  rem x7,a0,x6
  sub a0,a0,x7
  div a0,a0,x6

  jal x1,FUNCTION 
  lw a0,0(sp) #restore caller's n
  lw x1,8(sp)  #restore return address
  #computation for n>=10
  addi sp,sp,16 
  addi x6,x0,2
  mul a1,a1,x6
  addi x6,x0,7
  mul a0,a0,x6
  addi x6,x0,8
  div a0,a0,x6
  add a1,a1,a0
  addi a1,a1,-137
  beq x1,x0,__start
  jalr x0,0(x1)

L2:
  addi a0,a0,-1
  jal x1, FUNCTION
  lw a0,0(sp)
  lw x1,8(sp)
  addi sp,sp,16
  #computation for n>=10
  addi x6,x0,2
  mul a1,a1,x6
  beq x1,x0,__start
  jalr x0,0(x1)
  

#----------------------------------------------------Do not modify below text----------------------------------------------------
__start:
    la   t0, n
    lw   a0, 0(t0)
    jal  x1, FUNCTION
    la   t0, n
    sw   a1, 4(t0)
    li a7, 10
    ecall
