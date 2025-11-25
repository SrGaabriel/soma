
declare i32 @puts(ptr)
@str_4=private unnamed_addr constant [2 x i8] c"5\00"
@str_3=private unnamed_addr constant [2 x i8] c"1\00"
@str_2=private unnamed_addr constant [5 x i8] c"None\00"
@str_1=private unnamed_addr constant [7 x i8] c"<list>\00"
@str_0=private unnamed_addr constant [7 x i8] c"<list>\00"




define void @"main"() {
block0:
%tmp_reg_10 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_11 = ptrtoint ptr @str_4 to i64
%tmp_reg_12 = insertvalue {i8, i64} %tmp_reg_10, i64 %tmp_reg_11, 1
%tmp_reg_13 = call {i8, i64} @"fmap$Option$m55344248"(ptr @"lambda$0$m55344248", {i8, i64} %tmp_reg_12)
%tmp_reg_14 = alloca [5 x i32]
%tmp_reg_15 = getelementptr inbounds i32, ptr %tmp_reg_14, i32 0
store i32 5, ptr %tmp_reg_15
%tmp_reg_16 = getelementptr inbounds i32, ptr %tmp_reg_14, i32 1
store i32 4, ptr %tmp_reg_16
%tmp_reg_17 = getelementptr inbounds i32, ptr %tmp_reg_14, i32 2
store i32 3, ptr %tmp_reg_17
%tmp_reg_18 = getelementptr inbounds i32, ptr %tmp_reg_14, i32 3
store i32 2, ptr %tmp_reg_18
%tmp_reg_19 = getelementptr inbounds i32, ptr %tmp_reg_14, i32 4
store i32 1, ptr %tmp_reg_19
%tmp_reg_20 = call ptr @"display$Array$Array_Int$m55344248"(ptr %tmp_reg_14)
call i32 @puts(ptr %tmp_reg_20)
%tmp_reg_21 = call ptr @"display$Option$m55344248"({i8, i64} %tmp_reg_13)
call i32 @puts(ptr %tmp_reg_21)
ret void

}
define ptr @"lambda$0$m55344248"(ptr %x) {
entry:
ret ptr @str_3

}
define {i8, i64} @"fmap$Option$m55344248"(ptr %arg0,{i8, i64} %arg1) {
block4:
%tmp_reg_3 = extractvalue {i8, i64} %arg1, 0
switch i8 %tmp_reg_3, label %block6 [i8 1, label %block6 i8 0, label %block7]

block6:
ret {i8, i64} { i8 1, i64 0 }

block7:
%tmp_reg_4 = extractvalue {i8, i64} %arg1, 1
%tmp_reg_5 = inttoptr i64 %tmp_reg_4 to ptr
%tmp_reg_6 = call ptr %arg0(ptr %tmp_reg_5)
%tmp_reg_7 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_8 = ptrtoint ptr %tmp_reg_6 to i64
%tmp_reg_9 = insertvalue {i8, i64} %tmp_reg_7, i64 %tmp_reg_8, 1
ret {i8, i64} %tmp_reg_9

}
define ptr @"display$String$m55344248"(ptr %str) {
entry:
ret ptr %str

}
define ptr @"display$Option$m55344248"({i8, i64} %arg0) {
block0:
%tmp_reg_0 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_0, label %block2 [i8 1, label %block2 i8 0, label %block3]

block2:
ret ptr @str_2

block3:
%tmp_reg_1 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_2 = inttoptr i64 %tmp_reg_1 to ptr
ret ptr %tmp_reg_2

}
define ptr @"display$Array$Array_Int$m55344248"(ptr %list) {
entry:
ret ptr @str_1

}
define ptr @"display$Array$m55344248"(ptr %list) {
entry:
ret ptr @str_0

}
