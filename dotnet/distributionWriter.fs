namespace global

open System
open System.IO
open System.Text
open System.Threading.Tasks

[<AutoOpen>]
module internal WriterInternal =
    let inline writeAll ws v =
        for w in ws do (^w : (member Write : _ -> _) (w, v))

    let inline writeLineAll ws v =
        for w in ws do (^w : (member WriteLine : _ -> _) (w, v))

    let inline writeAsyncAll ws v =
        Array.map (fun w -> (^w : (member WriteAsync : _ -> _) (w, v))) ws
        |> Task.WhenAll

    let inline writeLineAsyncAll ws v =
        Array.map (fun w -> (^w : (member WriteLineAsync : _ -> _) (w, v))) ws
        |> Task.WhenAll

[<Sealed>]
type DistributionWriter(writers, leaveOpen) =
    inherit TextWriter()

    let ws = Seq.toArray writers

    new ([<ParamArray>] writers) = new DistributionWriter(Array.toSeq writers, false)
    new (writers) = new DistributionWriter(writers, false)

    override __.Encoding = Encoding.Default

    override x.Close() = x.Dispose true
    override __.Dispose disposing =
        base.Dispose disposing
        if leaveOpen then ()
        else
            for w: TextWriter in ws do w.Dispose()

    override __.Flush() = for w in ws do w.Flush()
    override __.FlushAsync() = ws |> Array.map (fun w -> w.FlushAsync()) |> Task.WhenAll

    override __.Write(value: bool) = writeAll ws value
    override __.Write(value: char) = writeAll ws value
    override __.Write(value: int) = writeAll ws value
    override __.Write(value: uint32) = writeAll ws value
    override __.Write(value: int64) = writeAll ws value
    override __.Write(value: uint64) = writeAll ws value
    override __.Write(value: single) = writeAll ws value
    override __.Write(value: double) = writeAll ws value
    override __.Write(value: decimal) = writeAll ws value
    override __.Write(value: obj) = writeAll ws value
    override __.Write(buffer: char array) = writeAll ws buffer
    override __.Write(buffer, index, count) = for w in ws do w.Write(buffer, index, count)
    override __.Write(value: string) = writeAll ws value
    override __.Write(format: string, arg0: obj) = for w in ws do w.Write(format, arg0)
    override __.Write(format: string, arg0: obj, arg1: obj) = for w in ws do w.Write(format, arg0, arg1)
    override __.Write(format, arg0, arg1, arg2) = for w in ws do w.Write(format, arg0, arg1, arg2)
    override __.Write(format, [<ParamArray>] args) = for w in ws do w.Write(format, args)

    override __.WriteLine() = for w in ws do w.WriteLine()
    override __.WriteLine(value: bool) = writeLineAll ws value
    override __.WriteLine(value: char) = writeLineAll ws value
    override __.WriteLine(value: int) = writeLineAll ws value
    override __.WriteLine(value: uint32) = writeLineAll ws value
    override __.WriteLine(value: int64) = writeLineAll ws value
    override __.WriteLine(value: uint64) = writeLineAll ws value
    override __.WriteLine(value: single) = writeLineAll ws value
    override __.WriteLine(value: double) = writeLineAll ws value
    override __.WriteLine(value: decimal) = writeLineAll ws value
    override __.WriteLine(buffer: char array) = writeLineAll ws buffer
    override __.WriteLine(buffer, index, count) = for w in ws do w.WriteLine(buffer, index, count)
    override __.WriteLine(value: string) = writeLineAll ws value
    override __.WriteLine(format: string, arg0: obj) = for w in ws do w.WriteLine(format, arg0)
    override __.WriteLine(format: string, arg0: obj, arg1: obj) = for w in ws do w.WriteLine(format, arg0, arg1)
    override __.WriteLine(format, arg0, arg1, arg2) = for w in ws do w.WriteLine(format, arg0, arg1, arg2)
    override __.WriteLine(format, [<ParamArray>] args) = for w in ws do w.WriteLine(format, args)
    override __.WriteLine(value: obj) = writeLineAll ws value

    override __.WriteAsync(value: char) = writeAsyncAll ws value
    override __.WriteAsync(value: string) = writeAsyncAll ws value
    override __.WriteAsync(buffer, index, count) = ws |> Array.map (fun w -> w.WriteAsync(buffer, index, count)) |> Task.WhenAll

    override __.WriteLineAsync(value: char) = writeLineAsyncAll ws value
    override __.WriteLineAsync(value: string) = writeLineAsyncAll ws value
    override __.WriteLineAsync(buffer, index, count) = ws |> Array.map (fun w -> w.WriteLineAsync(buffer, index, count)) |> Task.WhenAll
