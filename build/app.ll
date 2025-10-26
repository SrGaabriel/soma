

%Shape_dt = type {i8, [4 x i8]}


define %Shape_dt @testShape() {
%reg_52 = alloca %Shape_dt
%reg_53 = getelementptr %Shape_dt, ptr %reg_52, i32 0, i32 0
store i8 1, ptr %reg_53
%reg_54 = load %Shape_dt, ptr %reg_52
ret %Shape_dt %reg_54
}
define i1 @areNumEqual(i32 %reg_49,i32 %reg_50) {
%reg_51 = call i1 @Eq_989831974814699599_equals(i32 %reg_49, i32 %reg_50)
ret i1 %reg_51
}
define i32 @testSum(i32 %reg_46,i32 %reg_47) {
%reg_48 = add i32 %reg_46, %reg_47
ret i32 %reg_48
}
define i1 @Eq_5785918410229445819_equals(%Shape_dt %reg_6,%Shape_dt %reg_7) {
%reg_8 = alloca i1
%reg_9 = alloca %Shape_dt
store %Shape_dt %reg_6, ptr %reg_9
%reg_10 = getelementptr %Shape_dt, ptr %reg_9, i32 0, i32 0
%reg_11 = load i8, ptr %reg_10
switch i8 %reg_11, label %match.default.5 [i8 1, label %match.case.3 i8 0, label %match.case.4]
match.case.3:
%reg_12 = alloca i1
%reg_13 = alloca %Shape_dt
store %Shape_dt %reg_7, ptr %reg_13
%reg_14 = getelementptr %Shape_dt, ptr %reg_13, i32 0, i32 0
%reg_15 = load i8, ptr %reg_14
%reg_16 = icmp eq i8 %reg_15, 1
br i1 %reg_16, label %match.case.7, label %match.default.8
match.case.7:
%reg_17 = alloca %Shape_dt
store %Shape_dt %reg_6, ptr %reg_17
%reg_18 = getelementptr %Shape_dt, ptr %reg_17, i32 0, i32 1
%reg_19 = getelementptr i8, ptr %reg_18, i32 0
%reg_20 = bitcast ptr %reg_19 to ptr
%reg_21 = load i32, ptr %reg_20
%reg_22 = alloca %Shape_dt
store %Shape_dt %reg_7, ptr %reg_22
%reg_23 = getelementptr %Shape_dt, ptr %reg_22, i32 0, i32 1
%reg_24 = getelementptr i8, ptr %reg_23, i32 0
%reg_25 = bitcast ptr %reg_24 to ptr
%reg_26 = load i32, ptr %reg_25
%reg_27 = call i1 @Eq_989831974814699599_equals(i32 %reg_21, i32 %reg_26)
store i1 %reg_27, ptr %reg_12
br label %match.merge.9
match.default.8:
store i1 0, ptr %reg_12
br label %match.merge.9
match.merge.9:
%reg_28 = load i1, ptr %reg_12
store i1 %reg_28, ptr %reg_8
br label %match.merge.6
match.case.4:
%reg_29 = alloca i1
%reg_30 = alloca %Shape_dt
store %Shape_dt %reg_7, ptr %reg_30
%reg_31 = getelementptr %Shape_dt, ptr %reg_30, i32 0, i32 0
%reg_32 = load i8, ptr %reg_31
%reg_33 = icmp eq i8 %reg_32, 0
br i1 %reg_33, label %match.case.10, label %match.default.11
match.case.10:
%reg_34 = alloca %Shape_dt
store %Shape_dt %reg_6, ptr %reg_34
%reg_35 = getelementptr %Shape_dt, ptr %reg_34, i32 0, i32 1
%reg_36 = getelementptr i8, ptr %reg_35, i32 0
%reg_37 = bitcast ptr %reg_36 to ptr
%reg_38 = load i32, ptr %reg_37
%reg_39 = alloca %Shape_dt
store %Shape_dt %reg_7, ptr %reg_39
%reg_40 = getelementptr %Shape_dt, ptr %reg_39, i32 0, i32 1
%reg_41 = getelementptr i8, ptr %reg_40, i32 0
%reg_42 = bitcast ptr %reg_41 to ptr
%reg_43 = load i32, ptr %reg_42
store i1 1, ptr %reg_29
br label %match.merge.12
match.default.11:
store i1 0, ptr %reg_29
br label %match.merge.12
match.merge.12:
%reg_44 = load i1, ptr %reg_29
store i1 %reg_44, ptr %reg_8
br label %match.merge.6
match.default.5:
store i1 0, ptr %reg_8
br label %match.merge.6
match.merge.6:
%reg_45 = load i1, ptr %reg_8
ret i1 %reg_45
}
define i1 @Eq_989831974814699599_equals(i32 %reg_4,i32 %reg_5) {
ret i1 1
}
define i1 @isZero(i32 %reg_0) {
%reg_1 = alloca i1
%reg_2 = icmp eq i32 %reg_0, 0
br i1 %reg_2, label %match.case.0, label %match.default.1
match.case.0:
store i1 1, ptr %reg_1
br label %match.merge.2
match.default.1:
store i1 0, ptr %reg_1
br label %match.merge.2
match.merge.2:
%reg_3 = load i1, ptr %reg_1
ret i1 %reg_3
}
