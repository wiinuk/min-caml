.assembly extern mscorlib {}

.class public abstract sealed beforefieldinit MinCamlGlobal
{
    .method public static class [mscorlib]System.DBNull min_caml_print_newline(
        class [mscorlib]System.DBNull _arg1
    )
    cil managed
    {
        call void [mscorlib]System.Console::WriteLine()
        ldnull
        ret
    }

    .method public static class [mscorlib]System.DBNull min_caml_print_int(
        int32 x
    )
    cil managed
    {
        ldarg.0
        call void [mscorlib]System.Console::Write(int32)
        ldnull
        ret
    }

    .method public static class [mscorlib]System.DBNull min_caml_print_byte(
        int32 x
    )
    cil managed 
    {
        ldarg.0
        conv.ovf.u1
        conv.u2
        call void [mscorlib]System.Console::Write(char)
        ldnull
        ret
    }

    .method public static class [mscorlib]System.DBNull min_caml_prerr_int(
        int32 x
    )
    cil managed
    {
        call class [mscorlib]System.IO.TextWriter [mscorlib]System.Console::get_Error()
        ldarg.0
        callvirt instance void [mscorlib]System.IO.TextWriter::Write(int32)
        ldnull
        ret
    }

    .method public static class [mscorlib]System.DBNull min_caml_prerr_byte(
        int32 x
    )
    cil managed
    {
        call class [mscorlib]System.IO.TextWriter [mscorlib]System.Console::get_Error()
        ldarg.0
        conv.ovf.u1
        conv.u2
        callvirt instance void [mscorlib]System.IO.TextWriter::Write(char)
        ldnull
        ret
    }

    .method public static class [mscorlib]System.DBNull min_caml_prerr_float (
        float64 x
    )
    cil managed
    {
        call class [mscorlib]System.IO.TextWriter [mscorlib]System.Console::get_Error()
        ldarg.0
        callvirt instance void [mscorlib]System.IO.TextWriter::Write(float64)
        ldnull
        ret
    }

    .method public static int32 min_caml_read_int (
        class [mscorlib]System.DBNull _arg1
    )
    cil managed
    {
		call string [mscorlib]System.Console::ReadLine()
        call int32 [mscorlib]System.Int32::Parse(string)
        ret
    }

    .method public static float64 min_caml_read_float (
        class [mscorlib]System.DBNull _arg1
    )
    cil managed
    {
		call string [mscorlib]System.Console::ReadLine()
        call float64 [mscorlib]System.Double::Parse(string)
        ret
    }

    .method public static !!T[] min_caml_create_array<T>(
        int32 n,
        !!T x
    )
    cil managed
	{
		.maxstack 5
		.locals init (
			[0] !!T[] xs,
			[1] int32,
			[2] int32 i
		)

		ldarg.0
		newarr !!T
		stloc.0
		ldc.i4.0
		stloc.2
		ldarg.0
		ldc.i4.1
		sub
		stloc.1
		ldloc.1
		ldloc.2
		blt.s finish
			loopHead: ldloc.0
			ldloc.2
			ldarg.1
			stelem.any !!T
			ldloc.2
			ldc.i4.1
			add
			stloc.2
			ldloc.2
			ldloc.1
			ldc.i4.1
			add
			bne.un.s loopHead

		finish: ldloc.0
		ret
	}

    .method public static float64[] min_caml_create_float_array(
        int32 n,
        float64 x
    )
    cil managed
    {
        ldarg.0
        ldarg.1
        call !!0[] MinCamlGlobal::min_caml_create_array<float64>(int32, !!0)
        ret
    }

    .method public static float64 min_caml_abs_float(
        float64 x
    )
    cil managed
    {
        nop
        ldarg.0
        call float64 [mscorlib]System.Math::Abs(float64)
        ret
    }

    .method public static float64 min_caml_sqrt(
        float64 x
    )
    cil managed
    {
        ldarg.0
        call float64 [mscorlib]System.Math::Sqrt(float64)
        ret
    }

    .method public static float64 min_caml_floor(
        float64 x
    )
    cil managed
    {
        ldarg.0
        call float64 [mscorlib]System.Math::Floor(float64)
        ret
    }

    .method public static int32 min_caml_int_of_float(
        float64 x
    )
    cil managed
    {
        ldarg.0
        conv.i4
        ret
    }

    .method public static int32 min_caml_truncate(
        float64 x
    )
    cil managed
    {
        ldarg.0
        conv.i4
        ret
    }
    
    .method public static float64 min_caml_float_of_int(
        int32 x
    )
    cil managed
    {
        ldarg.0
        conv.r8
        ret
    }

    .method public static float64 min_caml_cos(
        float64 x
    )
    cil managed
    {
        ldarg.0
        call float64 [mscorlib]System.Math::Cos(float64)
        ret
    }

    .method public static float64 min_caml_sin(
        float64 x
    )
    cil managed
    {
        ldarg.0
        call float64 [mscorlib]System.Math::Sin(float64)
        ret
    }

    .method public static float64 min_caml_atan (
        float64 x
    )
    cil managed
    {
        ldarg.0
        call float64 [mscorlib]System.Math::Atan(float64)
        ret
    }
}
