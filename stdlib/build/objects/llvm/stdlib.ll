




define i32 @summing(i32 %x,i32 %y) {
entry:
%tmp_reg_0 = add i32 %x, %y
ret i32 %tmp_reg_0

}
define i32 @id(i32 %value) {
entry:
ret i32 %value

}
