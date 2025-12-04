
%SomaClosure = type {i8, i8, i16, i32, ptr}
@str_1=private unnamed_addr constant [5 x i8] c"None\00"
@str_0=private unnamed_addr constant [7 x i8] c"<list>\00"




define {i8, i64} @"fmap$Option$m22343894"(ptr %arg0,{i8, i64} %arg1) nounwind nosync nofree willreturn norecurse {
block6:
%tmp_reg_7 = extractvalue {i8, i64} %arg1, 0
switch i8 %tmp_reg_7, label %block8 [i8 0, label %block8 i8 1, label %block9]

block8:
%tmp_reg_8 = extractvalue {i8, i64} %arg1, 1
%tmp_reg_9 = inttoptr i64 %tmp_reg_8 to ptr
%tmp_reg_10 = getelementptr inbounds i64, ptr %tmp_reg_9, i64 1
%tmp_reg_11 = load i64, ptr %tmp_reg_10
%tmp_reg_12 = inttoptr i64 %tmp_reg_11 to ptr
%tmp_reg_13 = bitcast ptr %arg0 to ptr
%tmp_reg_14 = getelementptr inbounds %SomaClosure, ptr %tmp_reg_13, i32 0, i32 4
%tmp_reg_15 = load ptr, ptr %tmp_reg_14
%tmp_reg_16 = bitcast ptr %tmp_reg_15 to ptr
%tmp_reg_17 = call ptr %tmp_reg_16(ptr %arg0, ptr %tmp_reg_12)
%tmp_reg_18 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_19 = ptrtoint ptr %tmp_reg_17 to i64
%tmp_reg_20 = insertvalue {i8, i64} %tmp_reg_18, i64 %tmp_reg_19, 1
ret {i8, i64} %tmp_reg_20

block9:
%tmp_reg_21 = insertvalue {i8, i64} undef, i8 1, 0
ret {i8, i64} %tmp_reg_21

}
define ptr @"display$String$m22343894"(ptr %str) nounwind nosync nofree memory(none) willreturn norecurse {
block5:
ret ptr %str

}
define ptr @"display$Option$m22343894"({i8, i64} %arg0) nounwind nosync nofree willreturn norecurse {
block1:
%tmp_reg_0 = extractvalue {i8, i64} %arg0, 0
switch i8 %tmp_reg_0, label %block3 [i8 0, label %block3 i8 1, label %block4]

block3:
%tmp_reg_1 = extractvalue {i8, i64} %arg0, 1
%tmp_reg_2 = inttoptr i64 %tmp_reg_1 to ptr
%tmp_reg_3 = getelementptr inbounds i64, ptr %tmp_reg_2, i64 1
%tmp_reg_4 = load i64, ptr %tmp_reg_3
%tmp_reg_5 = inttoptr i64 %tmp_reg_4 to ptr
%tmp_reg_6 = tail call ptr @"display$m22343894"(ptr %tmp_reg_5)
ret ptr %tmp_reg_6

block4:
ret ptr @str_1

}
define ptr @"display$Array$m22343894"(ptr %list) nounwind nosync nofree memory(none) willreturn norecurse {
block0:
ret ptr @str_0

}
