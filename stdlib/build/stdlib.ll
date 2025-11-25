
@str_1=private unnamed_addr constant [5 x i8] c"None\00"
@str_0=private unnamed_addr constant [7 x i8] c"<list>\00"




define {i8, i64} @"fmap$Option$m33972100"(ptr %arg0,{i8, i64} %arg1) {
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
define ptr @"display$String$m33972100"(ptr %str) {
entry:
ret ptr %str

}
define ptr @"display$Option$m33972100"({i8, i64} %arg0) {
block0:
%tmp_reg_0 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_0, label %block2 [i8 1, label %block2 i8 0, label %block3]

block2:
ret ptr @str_1

block3:
%tmp_reg_1 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_2 = inttoptr i64 %tmp_reg_1 to ptr
ret ptr %tmp_reg_2

}
define ptr @"display$Array$m33972100"(ptr %list) {
entry:
ret ptr @str_0

}
