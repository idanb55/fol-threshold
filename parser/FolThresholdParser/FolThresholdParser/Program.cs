using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser
{
    public class Program
    {
        public static void Main(string[] args)
        {
            try
            {
                var inputFile = @"..\..\..\..\..\bosco2.folthreshold";
                //var outputDir = $@"..\..\..\..\..\out_{DateTime.Now:yyyy_MM_dd_HH_mm_ss}";
                var outputDir = $@"..\..\..\..\..\out";

                var system = new FolThresholdSystem.FolThresholdSystem();
                foreach (var t in Tokenizer.Tokenize(inputFile))
                {
                    system.ParseCode(t.ToArray());
                }

                if(Directory.Exists(outputDir)) Directory.Delete(outputDir, true);
                Directory.CreateDirectory(outputDir);

                File.AppendAllLines(Path.Combine(outputDir, "ivy.ivy"), system.ToIvyAxioms());

                int counter = 0;
                foreach (var specification in system.Formulas.Where(spec => spec.Conjecture))
                {
                    File.AppendAllLines(Path.Combine(outputDir, $"threshold_conjecture{counter:D5}.smt2"), system.AssertThresholdSmt2(specification));
                    counter++;
                }
                
                counter = 0;
                foreach (var specification in system.ProduceConjectures().Take(9999))
                {
                    File.AppendAllLines(Path.Combine(outputDir, $"auto_threshold_conjecture{counter:D5}.smt2"), system.AssertThresholdSmt2(specification));
                    counter++;
                }

                /**foreach (var bapaSetExpression in VennDiagram.VennDiagramIterator.GetVennZonesHelper(new []
                {
                    new SetVarExpression("A1"), new SetVarExpression("B1"), new SetVarExpression("C1"),
                }))
                {
                    Console.WriteLine(bapaSetExpression);
                    Console.Read();
                }**/
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex);
            }
            Console.WriteLine("Done.");
            Console.Read();
        }
    }
}
