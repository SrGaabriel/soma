declare ptr @malloc(i64)
@str_0=private unnamed_addr constant [9 x i8] c"No value\00"

%test_struct_syntax_Point_12 = type { i32, i32 }
%test_struct_syntax_Path_14 = type { ptr }



define i32 @"soma_main"() nounwind nosync nofree willreturn norecurse {
block16:
%tmp_reg_26 = call ptr @malloc(i64 8)
%tmp_reg_27 = bitcast ptr %tmp_reg_26 to ptr
%tmp_reg_28 = getelementptr inbounds %test_struct_syntax_Point_12, ptr %tmp_reg_27, i32 0, i32 0
store i32 10, ptr %tmp_reg_28
%tmp_reg_29 = getelementptr inbounds %test_struct_syntax_Point_12, ptr %tmp_reg_27, i32 0, i32 1
store i32 20, ptr %tmp_reg_29
%tmp_reg_30 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_31 = zext i32 5 to i64
%tmp_reg_32 = insertvalue {i8, i64} %tmp_reg_30, i64 %tmp_reg_31, 1
%tmp_reg_33 = call i32 @"test_struct_syntax_testPoint_28"(ptr %tmp_reg_27)
%tmp_reg_34 = call i32 @"test_struct_syntax_testTree_20"({i8, i64} %tmp_reg_32)
%tmp_reg_35 = add nsw i32 %tmp_reg_33, %tmp_reg_34
ret i32 %tmp_reg_35

}
define ptr @"test_struct_syntax_testPath_30"(ptr %p0) nounwind nosync nofree willreturn norecurse {
block15:
%tmp_reg_24 = getelementptr inbounds %test_struct_syntax_Path_14, ptr %p0, i32 0, i32 0
%tmp_reg_25 = load ptr, ptr %tmp_reg_24
ret ptr %tmp_reg_25

}
define i32 @"test_struct_syntax_testPoint_28"(ptr %p0) nounwind nosync nofree willreturn norecurse {
block14:
%tmp_reg_19 = getelementptr inbounds %test_struct_syntax_Point_12, ptr %p0, i32 0, i32 0
%tmp_reg_20 = load i32, ptr %tmp_reg_19
%tmp_reg_21 = getelementptr inbounds %test_struct_syntax_Point_12, ptr %p0, i32 0, i32 1
%tmp_reg_22 = load i32, ptr %tmp_reg_21
%tmp_reg_23 = add nsw i32 %tmp_reg_20, %tmp_reg_22
ret i32 %tmp_reg_23

}
define ptr @"test_struct_syntax_testDummy_25"({i8, i64} %p0) nounwind nosync nofree willreturn norecurse {
block8:
%tmp_reg_14 = extractvalue {i8, i64} %p0, 0
switch i8 %tmp_reg_14, label %block10 [i8 0, label %block10 i8 1, label %block11]

block10:
%tmp_reg_15 = extractvalue {i8, i64} %p0, 1
%tmp_reg_16 = inttoptr i64 %tmp_reg_15 to ptr
ret ptr %tmp_reg_16

block11:
%tmp_reg_17 = extractvalue {i8, i64} %p0, 1
%tmp_reg_18 = inttoptr i64 %tmp_reg_17 to ptr
ret ptr %tmp_reg_18

}
define ptr @"test_struct_syntax_testMaybe_22"({i8, i64} %p0) nounwind nosync nofree willreturn norecurse {
block4:
%tmp_reg_11 = extractvalue {i8, i64} %p0, 0
switch i8 %tmp_reg_11, label %block6 [i8 0, label %block6 i8 1, label %block7]

block6:
%tmp_reg_12 = extractvalue {i8, i64} %p0, 1
%tmp_reg_13 = inttoptr i64 %tmp_reg_12 to ptr
ret ptr %tmp_reg_13

block7:
ret ptr @str_0

}
define i32 @"test_struct_syntax_testTree_20"({i8, i64} %p0) nounwind nosync nofree willreturn norecurse {
block0:
%tmp_reg_0 = extractvalue {i8, i64} %p0, 0
switch i8 %tmp_reg_0, label %block2 [i8 0, label %block2 i8 1, label %block3]

block2:
%tmp_reg_1 = extractvalue {i8, i64} %p0, 1
%tmp_reg_2 = trunc i64 %tmp_reg_1 to i32
ret i32 %tmp_reg_2

block3:
%tmp_reg_3 = extractvalue {i8, i64} %p0, 1
%tmp_reg_4 = trunc i64 %tmp_reg_3 to i32
%tmp_reg_5 = extractvalue {i8, i64} %p0, 1
%tmp_reg_6 = inttoptr i64 %tmp_reg_5 to ptr
%tmp_reg_7 = getelementptr inbounds i64, ptr %tmp_reg_6, i64 1
%tmp_reg_8 = load i64, ptr %tmp_reg_7
%tmp_reg_9 = trunc i64 %tmp_reg_8 to i32
%tmp_reg_10 = add nsw i32 %tmp_reg_4, %tmp_reg_9
ret i32 %tmp_reg_10

}
