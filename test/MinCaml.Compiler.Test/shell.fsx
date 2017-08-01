[<AutoOpen>]
module Shell

open System
open System.IO

module shell =
    let mutable echo = true

module host =
    let out format = printfn format

type PathSplit =
    /// root name
    | Qualifier
    /// without root name
    | NoQualifier
    /// parent directory or root
    | Parent
    /// directory or file name
    | Leaf

type Path =
    static member Split(path, ?target) =
        match defaultArg target Parent with
        | Qualifier -> Path.GetPathRoot path
        | NoQualifier -> path.[Path.GetDirectoryName(path).Length..]
        | Parent -> Path.GetDirectoryName path
        | Leaf -> Path.GetFileName path

module path =
    let split x = Path.Split x
    let join x y = Path.Combine(x, y)
    let test p = File.Exists p || Directory.Exists p
    let changeExtension path newExtension = Path.ChangeExtension(path, newExtension)

module location =
    let get<'a> = Environment.CurrentDirectory
    let set x = Environment.CurrentDirectory <- x

type Recurse = Recurse | NoRecurse
type ChildItem =
    static member Get(p, ?recure) =
        let recure = defaultArg recure NoRecurse
        let parent, name = Path.GetDirectoryName p, Path.GetFileName p
        let parent = if parent = "" then "." else parent
        
        Directory.EnumerateFileSystemEntries(parent, name, if recure = Recurse then SearchOption.AllDirectories else SearchOption.TopDirectoryOnly)
        |> Seq.map (function
            | p when File.Exists p -> FileInfo p :> FileSystemInfo
            | p -> DirectoryInfo p :> _
        )

module childItem =
    let get p = ChildItem.Get p

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

module content =
    let add path format =
        Printf.kprintf (fun s ->
            let s = if s.EndsWith "\n" then s else s + "\r\n"
            File.AppendAllText(path, s)
        ) format

module date =
    let get<'a> = DateTime.Now

/// object
module obj =
    let foreach f xs = Seq.iter (f >> ignore) xs
    let select f xs = Seq.map f xs

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

    let log x = if shell.echo then writeText stdout ConsoleColor.Gray x
    let logfn format = Printf.ksprintf log format

    let start (p: Process) = 
        try Console.OutputEncoding <- Encoding.UTF8
        with e -> logfn "Failed setting UTF8 console encoding, ignoring error... %s." e.Message

        try p.Start() |> ignore
        with :? System.ComponentModel.Win32Exception as e -> failwithf "%A" p.StartInfo.FileName

    let invokeAsyncCore returnOut command args = async {
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

    let invokeAsync command = invokeAsyncCore true command |> Printf.kprintf
    let invoke command =
        invokeAsyncCore false command
        >> Async.RunSynchronously
        >> ignore
        |> Printf.kprintf

[<AutoOpen>]
module Toplevel =
    let echoOff<'a> = shell.echo <- false
    let echoOn<'a> = shell.echo <- true

[<AutoOpen>]
module DefaultAlias =
    /// location.set
    let cd p = location.set p
    /// location.get
    let pwd<'a> = location.get<'a>
    /// childItem.get
    let gci p = childItem.get p
    /// expression.invoke
    let exe command args = expression.invoke command args
    /// obj.foreach
    let foreach f xs = obj.foreach f xs
    let select f xs = obj.select f xs
    /// item.remove
    let del pattern = item.remove pattern

[<AutoOpen>]
module ShellOperators =
    let join separator xs = String.concat separator xs
    let f format = sprintf format

module ExtraOperators =
    /// path.join
    let (/) l r = path.join l r
    /// obj.foreach
    let (%) xs f = foreach f xs

[<AutoOpen>]
module ExternalPath =
    /// env:...
    let env x = Environment.GetEnvironmentVariable x
