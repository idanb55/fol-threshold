using System;
using System.Collections.Generic;
using System.Linq;

namespace FolThresholdParser
{
    public class Program
    {
        private static readonly Dictionary<string, Identifier> Identifiers = new Dictionary<string, Identifier>();
        private static readonly List<Formula> Formulas = new List<Formula>();

        public static void ParseCode(Token[] tokens)
        {
            if (tokens.Length == 0) return;

            var identifier = Identifier.Parse(tokens);
            if(identifier != null)
            {
                if (Identifiers.ContainsKey(identifier.Name))
                {
                    throw new MultipleDefinitionsOfIdentifier(tokens[0]);
                }
                Identifiers[identifier.Name] = identifier;
                return;
            }

            var formula = Formula.Parse(tokens);
            if (formula != null)
            {
                Formulas.Add(formula);
                return;
            }

            throw new Exception("Could not parse file");
        }

        public static void Main(string[] args)
        {
            foreach(var t in Tokenizer.Tokenize("..\\..\\..\\..\\..\\bosco2.folthreshold"))
            {
                ParseCode(t.ToArray());
            }
            Console.Read();
        }
    }
}
