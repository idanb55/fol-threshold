using System;
using System.IO;
using System.Linq;
using CommandLine;
using FolThresholdParser.FolThresholdSystem;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser
{
    public class Options
    {
        [Option('v', "verbose", Required = false, HelpText = "Set output to verbose messages.")]
        public bool Verbose { get; set; }

        [Option('o', "output", Required = true, HelpText = "Output directory")]
        public string OutputDir { get; set; }

        [Option('f', "input", Required = true, HelpText = "Threshold specification file")]
        public string TresholdSpecFilePath { get; set; }

        [Option('c', "cvc", Required = false, HelpText = "CVC4 solver path")]
        public string Cvc4Path { get; set; }
    }

    public class Program
    {
        public static Options Options;

        public static void Main(string[] args)
        {
            try
            {
                Options = new Options();
                CommandLine.Parser.Default.ParseArguments<Options>(args)
                    .WithParsed(Run)
                    .WithNotParsed(errs =>
                    {
                        foreach (var error in errs)
                        {
                            Console.WriteLine(error);
                        }
                    });
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex);
            }

            Console.WriteLine("Done.");
            Console.Read();
        }

        private static void Run(Options opts)
        {
            var system = new FolThresholdSystem.FolThresholdSystem();
            foreach (var t in Tokenizer.Tokenize(opts.TresholdSpecFilePath))
            {
                system.ParseCode(t.ToArray());
            }

            if (Directory.Exists(opts.OutputDir)) Directory.Delete(opts.OutputDir, true);
            Directory.CreateDirectory(opts.OutputDir);

            File.AppendAllLines(Path.Combine(opts.OutputDir, "ivy.ivy"), system.ToIvyAxioms());

            int counter = 0;
            foreach (var specification in system.Formulas.Where(spec => spec.Conjecture))
            {
                File.AppendAllLines(Path.Combine(opts.OutputDir, $"threshold_conjecture{counter:D5}.smt2"),
                    system.AssertThresholdSmt2(specification));
                counter++;
            }

            Directory.CreateDirectory(Path.Combine(opts.OutputDir, "auto_threshold_conjecture"));

            var total = 688;
            using (var ps = new ProgressBar())
            {
                foreach (var specification in system.ProduceConjectures().Take(total).Verify(system, ps))
                {
                    var resultThresholdPath = Path.Combine(opts.OutputDir, "auto_threshold_conjecture.threshold");

                    File.AppendAllLines(resultThresholdPath, new[] {specification.ToString()});
                }
            }
        }
    }
}
