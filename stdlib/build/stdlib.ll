
declare i32 @puts(ptr)
@str_0=private unnamed_addr constant [3 x i8] c"42\00"




define void @"test$m22343894"() nounwind nosync nofree willreturn norecurse {
block0:
%tmp_reg_0 = insertvalue {i8, i64} undef, i8 0, 0
%tmp_reg_1 = ptrtoint ptr @str_0 to i64
%tmp_reg_2 = insertvalue {i8, i64} %tmp_reg_0, i64 %tmp_reg_1, 1
%tmp_reg_3 = call ptr @"display$m22343894"({i8, i64} %tmp_reg_2)
call i32 @puts(ptr %tmp_reg_3)
ret void

}
