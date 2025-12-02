
declare i64 @inet_num_ext(i64)
declare i64 @inet_opr(ptr,ptr,i16,i64,i64)
declare i64 @inet_ref(ptr,ptr,i16,i64)
declare i64 @inet_get_num_ext(i64)
declare i64 @inet_closure(ptr,ptr,i16,i16,ptr,i16)
declare i64 @inet_app(ptr,ptr,i64,i64)
declare i64 @inet_closure_get_env(ptr,i64,i16)
declare i64 @inet_reduce(ptr,i64)
@g_inet = external global ptr
@g_inet_tm = external global ptr
declare void @inet_register_func(ptr,ptr,i16,ptr)
@str_4=private unnamed_addr constant [19 x i8] c"lambda$0$m33941000\00"
@str_3=private unnamed_addr constant [18 x i8] c"treeSum$m33941000\00"
@str_2=private unnamed_addr constant [22 x i8] c"sumWithBase$m33941000\00"
@str_1=private unnamed_addr constant [20 x i8] c"euclidGcd$m33941000\00"
@str_0=private unnamed_addr constant [17 x i8] c"divMod$m33941000\00"




define i64 @"treeSum$m33941000"(ptr %net,ptr %tm,i64 %arg) {
block9:
%tmp_reg_142 = call i64 @inet_get_num_ext(i64 %arg)
%tmp_reg_143 = trunc i64 %tmp_reg_142 to i32
%tmp_reg_144 = add i32 0, 0
%tmp_reg_145 = icmp eq i32 %tmp_reg_143, %tmp_reg_144
%tmp_reg_146 = select i1 %tmp_reg_145, i32 1, i32 0
%tmp_reg_147 = call i64 @inet_get_num_ext(i32 %tmp_reg_146)
%tmp_reg_148 = trunc i64 %tmp_reg_147 to i32
switch i32 %tmp_reg_148, label %block11 [i32 0, label %block11 i32 1, label %block12]

block11:
%tmp_reg_149 = add i32 1, 0
%tmp_reg_150 = sub i32 %tmp_reg_143, %tmp_reg_149
%tmp_reg_151 = sext i32 %tmp_reg_150 to i64
%tmp_reg_152 = call i64 @inet_num_ext(i64 %tmp_reg_151)
%tmp_reg_153 = call i64 @inet_ref(ptr %net, ptr %tm, i16 3, i64 %tmp_reg_152)
%tmp_reg_154 = add i32 1, 0
%tmp_reg_155 = sub i32 %tmp_reg_143, %tmp_reg_154
%tmp_reg_156 = sext i32 %tmp_reg_155 to i64
%tmp_reg_157 = call i64 @inet_num_ext(i64 %tmp_reg_156)
%tmp_reg_158 = call i64 @inet_ref(ptr %net, ptr %tm, i16 3, i64 %tmp_reg_157)
%tmp_reg_159 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_153, i64 %tmp_reg_158)
ret i64 %tmp_reg_159

block12:
%tmp_reg_160 = sext i32 1 to i64
%tmp_reg_161 = call i64 @inet_num_ext(i64 %tmp_reg_160)
ret i64 %tmp_reg_161

}
define i64 @"sumWithBase$m33941000"(ptr %net,ptr %tm,i64 %arg) {
block5:
%tmp_reg_109 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 0)
%tmp_reg_110 = call i64 @inet_get_num_ext(i64 %tmp_reg_109)
%tmp_reg_111 = trunc i64 %tmp_reg_110 to i32
%tmp_reg_112 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 1)
%tmp_reg_113 = call i64 @inet_get_num_ext(i64 %tmp_reg_112)
%tmp_reg_114 = trunc i64 %tmp_reg_113 to i32
%tmp_reg_115 = add i32 0, 0
%tmp_reg_116 = icmp eq i32 %tmp_reg_114, %tmp_reg_115
%tmp_reg_117 = select i1 %tmp_reg_116, i32 1, i32 0
%tmp_reg_118 = call i64 @inet_get_num_ext(i32 %tmp_reg_117)
%tmp_reg_119 = trunc i64 %tmp_reg_118 to i32
switch i32 %tmp_reg_119, label %block7 [i32 0, label %block7 i32 1, label %block8]

block7:
%tmp_reg_120 = sext i32 %tmp_reg_111 to i64
%tmp_reg_121 = call i64 @inet_num_ext(i64 %tmp_reg_120)
%tmp_reg_122 = alloca i64, i32 1
%tmp_reg_123 = getelementptr i64, ptr %tmp_reg_122, i64 0
store i64 %tmp_reg_121, ptr %tmp_reg_123
%tmp_reg_124 = call i64 @inet_closure(ptr %net, ptr %tm, i16 4, i16 1, ptr %tmp_reg_122, i16 1)
%tmp_reg_125 = sext i32 %tmp_reg_114 to i64
%tmp_reg_126 = call i64 @inet_num_ext(i64 %tmp_reg_125)
%tmp_reg_127 = call i64 @inet_app(ptr %net, ptr %tm, i64 %tmp_reg_124, i64 %tmp_reg_126)
%tmp_reg_128 = sext i32 %tmp_reg_111 to i64
%tmp_reg_129 = call i64 @inet_num_ext(i64 %tmp_reg_128)
%tmp_reg_130 = add i32 1, 0
%tmp_reg_131 = sub i32 %tmp_reg_114, %tmp_reg_130
%tmp_reg_132 = sext i32 %tmp_reg_131 to i64
%tmp_reg_133 = call i64 @inet_num_ext(i64 %tmp_reg_132)
%tmp_reg_134 = alloca i64, i32 2
%tmp_reg_135 = getelementptr i64, ptr %tmp_reg_134, i64 0
store i64 %tmp_reg_129, ptr %tmp_reg_135
%tmp_reg_136 = getelementptr i64, ptr %tmp_reg_134, i64 1
store i64 %tmp_reg_133, ptr %tmp_reg_136
%tmp_reg_137 = call i64 @inet_closure(ptr %net, ptr %tm, i16 2, i16 0, ptr %tmp_reg_134, i16 2)
%tmp_reg_138 = call i64 @inet_ref(ptr %net, ptr %tm, i16 2, i64 %tmp_reg_137)
%tmp_reg_139 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_127, i64 %tmp_reg_138)
ret i64 %tmp_reg_139

block8:
%tmp_reg_140 = sext i32 %tmp_reg_111 to i64
%tmp_reg_141 = call i64 @inet_num_ext(i64 %tmp_reg_140)
ret i64 %tmp_reg_141

}
define i32 @"soma_main"() {
block14:
%tmp_reg_43 = load ptr, ptr @g_inet
%tmp_reg_44 = select i1 true, ptr @"divMod$m33941000", ptr @"divMod$m33941000"
call void @inet_register_func(ptr %tmp_reg_43, ptr @str_0, i16 2, ptr %tmp_reg_44)
%tmp_reg_45 = load ptr, ptr @g_inet
%tmp_reg_46 = select i1 true, ptr @"euclidGcd$m33941000", ptr @"euclidGcd$m33941000"
call void @inet_register_func(ptr %tmp_reg_45, ptr @str_1, i16 2, ptr %tmp_reg_46)
%tmp_reg_47 = load ptr, ptr @g_inet
%tmp_reg_48 = select i1 true, ptr @"sumWithBase$m33941000", ptr @"sumWithBase$m33941000"
call void @inet_register_func(ptr %tmp_reg_47, ptr @str_2, i16 2, ptr %tmp_reg_48)
%tmp_reg_49 = load ptr, ptr @g_inet
%tmp_reg_50 = select i1 true, ptr @"treeSum$m33941000", ptr @"treeSum$m33941000"
call void @inet_register_func(ptr %tmp_reg_49, ptr @str_3, i16 1, ptr %tmp_reg_50)
%tmp_reg_51 = load ptr, ptr @g_inet
%tmp_reg_52 = select i1 true, ptr @"lambda$0$m33941000", ptr @"lambda$0$m33941000"
call void @inet_register_func(ptr %tmp_reg_51, ptr @str_4, i16 2, ptr %tmp_reg_52)
%tmp_reg_53 = sext i32 100 to i64
%tmp_reg_54 = call i64 @inet_num_ext(i64 %tmp_reg_53)
%tmp_reg_55 = sext i32 7 to i64
%tmp_reg_56 = call i64 @inet_num_ext(i64 %tmp_reg_55)
%tmp_reg_57 = load ptr, ptr @g_inet
%tmp_reg_58 = load ptr, ptr @g_inet_tm
%tmp_reg_59 = alloca i64, i32 2
%tmp_reg_60 = getelementptr i64, ptr %tmp_reg_59, i64 0
store i64 %tmp_reg_54, ptr %tmp_reg_60
%tmp_reg_61 = getelementptr i64, ptr %tmp_reg_59, i64 1
store i64 %tmp_reg_56, ptr %tmp_reg_61
%tmp_reg_62 = call i64 @inet_closure(ptr %tmp_reg_57, ptr %tmp_reg_58, i16 0, i16 0, ptr %tmp_reg_59, i16 2)
%tmp_reg_63 = load ptr, ptr @g_inet
%tmp_reg_64 = load ptr, ptr @g_inet_tm
%tmp_reg_65 = call i64 @inet_ref(ptr %tmp_reg_63, ptr %tmp_reg_64, i16 0, i64 %tmp_reg_62)
%tmp_reg_66 = sext i32 48 to i64
%tmp_reg_67 = call i64 @inet_num_ext(i64 %tmp_reg_66)
%tmp_reg_68 = sext i32 18 to i64
%tmp_reg_69 = call i64 @inet_num_ext(i64 %tmp_reg_68)
%tmp_reg_70 = load ptr, ptr @g_inet
%tmp_reg_71 = load ptr, ptr @g_inet_tm
%tmp_reg_72 = alloca i64, i32 2
%tmp_reg_73 = getelementptr i64, ptr %tmp_reg_72, i64 0
store i64 %tmp_reg_67, ptr %tmp_reg_73
%tmp_reg_74 = getelementptr i64, ptr %tmp_reg_72, i64 1
store i64 %tmp_reg_69, ptr %tmp_reg_74
%tmp_reg_75 = call i64 @inet_closure(ptr %tmp_reg_70, ptr %tmp_reg_71, i16 1, i16 0, ptr %tmp_reg_72, i16 2)
%tmp_reg_76 = load ptr, ptr @g_inet
%tmp_reg_77 = load ptr, ptr @g_inet_tm
%tmp_reg_78 = call i64 @inet_ref(ptr %tmp_reg_76, ptr %tmp_reg_77, i16 1, i64 %tmp_reg_75)
%tmp_reg_79 = sext i32 10 to i64
%tmp_reg_80 = call i64 @inet_num_ext(i64 %tmp_reg_79)
%tmp_reg_81 = sext i32 5 to i64
%tmp_reg_82 = call i64 @inet_num_ext(i64 %tmp_reg_81)
%tmp_reg_83 = load ptr, ptr @g_inet
%tmp_reg_84 = load ptr, ptr @g_inet_tm
%tmp_reg_85 = alloca i64, i32 2
%tmp_reg_86 = getelementptr i64, ptr %tmp_reg_85, i64 0
store i64 %tmp_reg_80, ptr %tmp_reg_86
%tmp_reg_87 = getelementptr i64, ptr %tmp_reg_85, i64 1
store i64 %tmp_reg_82, ptr %tmp_reg_87
%tmp_reg_88 = call i64 @inet_closure(ptr %tmp_reg_83, ptr %tmp_reg_84, i16 2, i16 0, ptr %tmp_reg_85, i16 2)
%tmp_reg_89 = load ptr, ptr @g_inet
%tmp_reg_90 = load ptr, ptr @g_inet_tm
%tmp_reg_91 = call i64 @inet_ref(ptr %tmp_reg_89, ptr %tmp_reg_90, i16 2, i64 %tmp_reg_88)
%tmp_reg_92 = sext i32 4 to i64
%tmp_reg_93 = call i64 @inet_num_ext(i64 %tmp_reg_92)
%tmp_reg_94 = load ptr, ptr @g_inet
%tmp_reg_95 = load ptr, ptr @g_inet_tm
%tmp_reg_96 = call i64 @inet_ref(ptr %tmp_reg_94, ptr %tmp_reg_95, i16 3, i64 %tmp_reg_93)
%tmp_reg_97 = load ptr, ptr @g_inet
%tmp_reg_98 = load ptr, ptr @g_inet_tm
%tmp_reg_99 = call i64 @inet_opr(ptr %tmp_reg_97, ptr %tmp_reg_98, i16 0, i64 %tmp_reg_65, i64 %tmp_reg_78)
%tmp_reg_100 = load ptr, ptr @g_inet
%tmp_reg_101 = load ptr, ptr @g_inet_tm
%tmp_reg_102 = call i64 @inet_opr(ptr %tmp_reg_100, ptr %tmp_reg_101, i16 0, i64 %tmp_reg_99, i64 %tmp_reg_91)
%tmp_reg_103 = load ptr, ptr @g_inet
%tmp_reg_104 = load ptr, ptr @g_inet_tm
%tmp_reg_105 = call i64 @inet_opr(ptr %tmp_reg_103, ptr %tmp_reg_104, i16 0, i64 %tmp_reg_102, i64 %tmp_reg_96)
%tmp_reg_106 = load ptr, ptr @g_inet
%tmp_reg_107 = call i64 @inet_reduce(ptr %tmp_reg_106, i64 %tmp_reg_105)
%tmp_reg_108 = trunc i64 %tmp_reg_107 to i32
ret i32 %tmp_reg_108

}
define i64 @"lambda$0$m33941000"(ptr %net,ptr %tm,i64 %arg) {
block13:
%tmp_reg_36 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 1)
%tmp_reg_37 = call i64 @inet_get_num_ext(i64 %tmp_reg_36)
%tmp_reg_38 = trunc i64 %tmp_reg_37 to i32
%tmp_reg_39 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 0)
%tmp_reg_40 = sext i32 %tmp_reg_38 to i64
%tmp_reg_41 = call i64 @inet_num_ext(i64 %tmp_reg_40)
%tmp_reg_42 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_41, i64 %tmp_reg_39)
ret i64 %tmp_reg_42

}
define i64 @"euclidGcd$m33941000"(ptr %net,ptr %tm,i64 %arg) {
block1:
%tmp_reg_13 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 0)
%tmp_reg_14 = call i64 @inet_get_num_ext(i64 %tmp_reg_13)
%tmp_reg_15 = trunc i64 %tmp_reg_14 to i32
%tmp_reg_16 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 1)
%tmp_reg_17 = call i64 @inet_get_num_ext(i64 %tmp_reg_16)
%tmp_reg_18 = trunc i64 %tmp_reg_17 to i32
%tmp_reg_19 = add i32 0, 0
%tmp_reg_20 = icmp eq i32 %tmp_reg_18, %tmp_reg_19
%tmp_reg_21 = select i1 %tmp_reg_20, i32 1, i32 0
%tmp_reg_22 = call i64 @inet_get_num_ext(i32 %tmp_reg_21)
%tmp_reg_23 = trunc i64 %tmp_reg_22 to i32
switch i32 %tmp_reg_23, label %block3 [i32 0, label %block3 i32 1, label %block4]

block3:
%tmp_reg_24 = sext i32 %tmp_reg_18 to i64
%tmp_reg_25 = call i64 @inet_num_ext(i64 %tmp_reg_24)
%tmp_reg_26 = srem i32 %tmp_reg_15, %tmp_reg_18
%tmp_reg_27 = sext i32 %tmp_reg_26 to i64
%tmp_reg_28 = call i64 @inet_num_ext(i64 %tmp_reg_27)
%tmp_reg_29 = alloca i64, i32 2
%tmp_reg_30 = getelementptr i64, ptr %tmp_reg_29, i64 0
store i64 %tmp_reg_25, ptr %tmp_reg_30
%tmp_reg_31 = getelementptr i64, ptr %tmp_reg_29, i64 1
store i64 %tmp_reg_28, ptr %tmp_reg_31
%tmp_reg_32 = call i64 @inet_closure(ptr %net, ptr %tm, i16 1, i16 0, ptr %tmp_reg_29, i16 2)
%tmp_reg_33 = call i64 @inet_ref(ptr %net, ptr %tm, i16 1, i64 %tmp_reg_32)
ret i64 %tmp_reg_33

block4:
%tmp_reg_34 = sext i32 %tmp_reg_15 to i64
%tmp_reg_35 = call i64 @inet_num_ext(i64 %tmp_reg_34)
ret i64 %tmp_reg_35

}
define i64 @"divMod$m33941000"(ptr %net,ptr %tm,i64 %arg) {
block0:
%tmp_reg_0 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 0)
%tmp_reg_1 = call i64 @inet_get_num_ext(i64 %tmp_reg_0)
%tmp_reg_2 = trunc i64 %tmp_reg_1 to i32
%tmp_reg_3 = call i64 @inet_closure_get_env(ptr %net, i64 %arg, i16 1)
%tmp_reg_4 = call i64 @inet_get_num_ext(i64 %tmp_reg_3)
%tmp_reg_5 = trunc i64 %tmp_reg_4 to i32
%tmp_reg_6 = sdiv i32 %tmp_reg_2, %tmp_reg_5
%tmp_reg_7 = sext i32 %tmp_reg_6 to i64
%tmp_reg_8 = call i64 @inet_num_ext(i64 %tmp_reg_7)
%tmp_reg_9 = srem i32 %tmp_reg_2, %tmp_reg_5
%tmp_reg_10 = sext i32 %tmp_reg_9 to i64
%tmp_reg_11 = call i64 @inet_num_ext(i64 %tmp_reg_10)
%tmp_reg_12 = call i64 @inet_opr(ptr %net, ptr %tm, i16 0, i64 %tmp_reg_8, i64 %tmp_reg_11)
ret i64 %tmp_reg_12

}
