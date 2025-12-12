using Microsoft.Boogie;

/// <summary>
/// Boogie command-line options (other tools can subclass this class in order to support a
/// superset of Boogie's options).
/// </summary>
public static class Clo 
{
    public static CommandLineOptions clo = new CommandLineOptions(System.Console.Out, new ConsolePrinter());
    public static int RecBound = 500;
    public static bool DoModSetAnalysis = false;
}