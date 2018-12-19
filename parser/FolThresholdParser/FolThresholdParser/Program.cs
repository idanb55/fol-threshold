using System;
using System.Linq;
using System.Windows.Forms;
using FolThresholdParser.Parser;

namespace FolThresholdParser
{
    public class Program
    {
        public static void Main(string[] args)
        {
            try
            {
                var system = new FolThresholdSystem();
                foreach (var t in Tokenizer.Tokenize("..\\..\\..\\..\\..\\bosco2.folthreshold"))
                {
                    system.ParseCode(t.ToArray());
                }

                Console.WriteLine(system.ToBapaFormula().ToOcamlBapa());
                Console.WriteLine();
                foreach (var ivyAxiom in system.ToIvyAxioms())
                {
                    Console.WriteLine(ivyAxiom);
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine(ex);
            }

            Console.Read();
        }
    }
}
