define i1 @areNumEqual(i32 %reg_3,i32 %reg_4) {
    %reg_5 = call i1 @==(i32 %reg_4,i32 %reg_3)
    ret i1 %reg_5
}

define i32 @testSum(i32 %reg_0,i32 %reg_1) {
    %reg_2 = call i32 @+(i32 %reg_1,i32 %reg_0)
    ret i32 %reg_2
}