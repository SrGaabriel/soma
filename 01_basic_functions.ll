




define i32 @"square$m75129668"(i32 %n) {
entry:
%tmp_reg_11 = mul i32 %n, %n
ret i32 %tmp_reg_11

}
define i32 @"fibonacci$m75129668"(i32 %arg0) {
block4:
switch i32 %arg0, label %block8 [i32 0, label %block6 i32 1, label %block7]

block6:
ret i32 0

block7:
ret i32 1

block8:
%tmp_reg_6 = sub i32 %arg0, 1
%tmp_reg_7 = call i32 @"fibonacci$m75129668"(i32 %tmp_reg_6)
%tmp_reg_8 = sub i32 %arg0, 2
%tmp_reg_9 = call i32 @"fibonacci$m75129668"(i32 %tmp_reg_8)
%tmp_reg_10 = add i32 %tmp_reg_7, %tmp_reg_9
ret i32 %tmp_reg_10

}
define i32 @"double$m75129668"(i32 %arg0) {
block2:
%tmp_reg_5 = add i32 %arg0, %arg0
ret i32 %tmp_reg_5

}
define i32 @"composed$m75129668"(i32 %x) {
entry:
%tmp_reg_3 = call i32 @"double$m75129668"(i32 %x)
%tmp_reg_4 = call i32 @"square$m75129668"(i32 %tmp_reg_3)
ret i32 %tmp_reg_4

}
define i32 @"applyTwice$m75129668"(ptr %arg0,i32 %arg1) {
block0:
%tmp_reg_1 = call i32 %arg0(i32 %arg1)
%tmp_reg_2 = call i32 %arg0(i32 %tmp_reg_1)
ret i32 %tmp_reg_2

}
define i32 @"add$m75129668"(i32 %x,i32 %y) {
entry:
%tmp_reg_0 = add i32 %x, %y
ret i32 %tmp_reg_0

}
