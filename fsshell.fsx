[<AutoOpen>]
module FsShell

open System
open System.IO

module fsshell =
    let mutable echo = true

module host =
    let out format = printfn format

module path =
    let split x = Path.GetDirectoryName x
    let join x y = Path.Combine(x, y)
    let test p = File.Exists p || Directory.Exists p

module location =
    let get<'a> = Environment.CurrentDirectory
    let set x = Environment.CurrentDirectory <- x

module childItem =
    let get p =
        let p =
            if Path.IsPathRooted p
            then Path.GetDirectoryName p, Path.GetFileName p
            else location.get, p
        p
        |> Directory.EnumerateFileSystemEntries
        |> Seq.map (function
            | p when File.Exists p -> FileInfo p :> FileSystemInfo
            | p -> DirectoryInfo p :> _
        )

type Item =
    static member Move(source, sink, ?force) =
        let force = defaultArg force false
        if force && File.Exists sink then File.Delete sink
        File.Move(source, sink)

    static member Remove(pattern, ?recurse) =
        let recurse = defaultArg recurse false

        childItem.get pattern
        |> Seq.iter (function
            | :? DirectoryInfo as x -> x.Delete recurse
            | x -> x.Delete()
        )

module item =
    let move source sink = File.Move(source, sink)
    let remove source = Item.Remove source

module private expressionInternal =
    open System.Diagnostics
    open System.Threading
    open System.Text

    let noNull = function null -> false | _ -> true

    let synchronize f = 
        let c1 = SynchronizationContext.Current
        f <| fun g -> 

        let c2 = SynchronizationContext.Current
        if noNull c1 && c1 <> c2 then c1.Post((fun _ -> g()), null)
        else g()

    let subscribe o (e: _ IObservable) = e.Subscribe o
    let dispose (x: IDisposable) = x.Dispose()

    let guardedAwaitObservable e guardFunction = 
        let removeObj = ref None
        let removeLock = obj()
        let setRemover r = lock removeLock <| fun _ -> removeObj := Some r
        
        let remove() = lock removeLock <| fun _ -> 
            match !removeObj with
            | None -> ()
            | Some d -> 
                removeObj := None
                dispose d

        synchronize <| fun f -> 

        let workflow = Async.FromContinuations <| fun (cont, econt, ccont) -> 
            let rec finish cont value = 
                remove()
                f <| fun _ -> cont value

            e
            |> subscribe { new IObserver<_> with
                member __.OnNext v = finish cont v
                member __.OnError e = finish econt e
                member __.OnCompleted() = 
                    "Cancelling the workflow, because the Observable awaited using AwaitObservable has completed."
                    |> OperationCanceledException
                    |> finish ccont
            }
            |> setRemover

            guardFunction()

        async {
            let! t = Async.CancellationToken
            use _ = t.Register(fun _ -> remove())
            return! workflow
        }
        
    let writeText (printer: TextWriter) color text =
        let old = Console.ForegroundColor
        try
            if old <> color then Console.ForegroundColor <- color
            printer.WriteLine(text: string)
        finally
            if old <> color then Console.ForegroundColor <- old

    let log x = if fsshell.echo then writeText stdout ConsoleColor.Gray x
    let logfn format = Printf.ksprintf log format

    let start (p: Process) = 
        try Console.OutputEncoding <- Encoding.UTF8
        with e -> logfn "Failed setting UTF8 console encoding, ignoring error... %s." e.Message

        p.Start() |> ignore

    let invokeAsyncCore command args returnOut = async {
        let info =
            ProcessStartInfo(
                command,
                UseShellExecute = false,
                RedirectStandardError = true,
                RedirectStandardOutput = true,
                RedirectStandardInput = true,
                WindowStyle = ProcessWindowStyle.Hidden,
                // WorkingDirectory = ...,
                Arguments = args
            )
        let p = new Process(StartInfo = info)
        let out = StringBuilder()
        let gate = obj()
        try
            p.ErrorDataReceived.Add <| fun e ->
                if noNull e.Data then writeText stderr ConsoleColor.Red e.Data

            p.OutputDataReceived.Add <| fun e ->
                match e.Data with
                | null -> ()
                | x ->
                    lock gate <| fun _ ->
                        out.AppendLine x |> ignore
                    log x

            start p
            p.BeginOutputReadLine()
            p.BeginErrorReadLine()
            p.StandardInput.Dispose()

            let! _ = guardedAwaitObservable p.Exited <| fun _ -> p.EnableRaisingEvents <- true
            return if returnOut then string out else string p.ExitCode

        finally
            Async.Sleep 10 |> Async.RunSynchronously
            p.Dispose()
    }


module expression =
    open expressionInternal

    let invokeAsync command = Printf.kprintf <| invokeAsyncCore command
    let invoke command = Printf.kprintf <| fun args ->
        invokeAsyncCore command args false
        |> Async.RunSynchronously

[<AutoOpen>]
module Toplevel =
    let echoOff<'a> = fsshell.echo <- false
    let echoOn<'a> = fsshell.echo <- true

[<AutoOpen>]
module DefaultAlias =
    let cd p = location.set p
    let pwd<'a> = location.get<'a>
    let gci p = childItem.get p
    let exe command args = expression.invoke command args
    let foreach f xs = Seq.iter (f >> ignore) xs
    let del pattern = item.remove pattern

[<AutoOpen>]
module ExternalPath =
    let env x = Environment.GetEnvironmentVariable x
