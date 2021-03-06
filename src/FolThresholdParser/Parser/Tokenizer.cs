﻿using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

namespace FolThresholdParser.Parser
{
    public class Tokenizer : IEnumerable<Token>
    {
        public static IEnumerable<IEnumerable<Token>> Tokenize(string filePath)
        {
            return File.ReadLines(filePath).Select((line, count) => new Tokenizer(line, count));
        }            

        public Tokenizer(string code, int line)
        {
            _line = line;

            var commentMatch = CommentRegex.Match(code);
            if (commentMatch.Success) code = code.Substring(0, commentMatch.Index);
            _code = code;
        }

        private readonly string _code;

        private int _cursor;
        private readonly int _line;

        private const string CommentString = "#";
        private static readonly Regex CommentRegex = new Regex(Regex.Escape(CommentString) + ".*");

        private readonly Dictionary<SyntaxKind, Regex> _patterns = new Dictionary<SyntaxKind, Regex>
        {
            {SyntaxKind.VariableNameToken,     new Regex("^[a-zA-Z_]+")},            
            {SyntaxKind.LiteralNumberToken,   new Regex("^[0-9]+")   },
            {SyntaxKind.WhitespaceToken,   new Regex("^\\s+")   }
        };

        public static readonly Dictionary<SyntaxKind, string> Keywords = new Dictionary<SyntaxKind, string>
        {
            // keywords
            {SyntaxKind.ConstantKeyword, "constant"},
            {SyntaxKind.NaturalKeyword, "natural"},
            {SyntaxKind.QuorumKeyword, "quorum"},
            {SyntaxKind.AxiomKeyword, "axiom"},
            {SyntaxKind.ConjectureKeyword, "conjecture"},
            {SyntaxKind.NonEmptyKeyword, "nonempty"},
            {SyntaxKind.SetKeyword, "set"},
            {SyntaxKind.NotKeyword, "not"},
            {SyntaxKind.AndKeyword, "and"},
            {SyntaxKind.OrKeyword, "or"},
            {SyntaxKind.ForallSetKeyword, "forall"},
            {SyntaxKind.ExistsSetKeyword, "exists"},

            // operation
            { SyntaxKind.OpenParenthesisToken,         ("(")         },
            { SyntaxKind.CloseParenthesisToken,     (")")         },

            { SyntaxKind.DotToken,          (".")        },
            { SyntaxKind.CommaToken,          (",")        },
            { SyntaxKind.ColonToken,          (":")        },

            { SyntaxKind.PlusOperationToken,          ("+")        },
            { SyntaxKind.MinusOperationToken,         ("-")        },
            { SyntaxKind.DivOperationToken,          ("/")        },
            { SyntaxKind.AndOperationToken,          ("&")        },
            { SyntaxKind.OrOperationToken,         ("|")        },
            { SyntaxKind.ComplementOperationToken,         ("~")        },

            { SyntaxKind.EqualToken,                 ("=")            },
            { SyntaxKind.InEqualToken,              ("!=")         },

            { SyntaxKind.GeqThanToken,              (">=")         },
            { SyntaxKind.GreaterThanToken,              (">")         },

            { SyntaxKind.LeqThanToken,              ("<=")         },
            { SyntaxKind.LessThanToken,              ("<")         }
            
        };

        private int MatchesConst(SyntaxKind kind)
        {
            var length = Keywords[kind].Length;
            if (_code.Length >= _cursor + length && Keywords[kind].Equals(_code.Substring(_cursor, length))) return length;
            return 0;
        }

        private int MatchesPattern(SyntaxKind kind)
        {
            var match = _patterns[kind].Match(_code.Substring(_cursor));
            return match.Success ? match.Length : 0;
        }

        private Token MakeToken(SyntaxKind kind, int length)
        {
            var res = new Token(_cursor, length, kind, _code, _line);
            _cursor += length;
            return res;
        }

        private Token NextToken()
        {
            foreach (var kind in Keywords.Keys)
            {
                var length = MatchesConst(kind);
                if (length <= 0) continue;
                return MakeToken(kind, length);
            }

            foreach (var kind in _patterns.Keys)
            {
                var length = MatchesPattern(kind);
                if (length <= 0) continue;
                return MakeToken(kind, length);
            }

            throw new CountNotTokenizeCharException(_code, _cursor);            
        }

        public IEnumerable<Token> Tokenize()
        {
            for (_cursor = 0; _cursor < _code.Length;)
            {
                var savedCursor = _cursor;

                var token = NextToken();
                if (token != null && token.Type != SyntaxKind.WhitespaceToken) yield return token;
                                
                if (savedCursor == _cursor)
                    throw new CountNotTokenizeCharException(_code, _cursor);
            }
        }

        public IEnumerator<Token> GetEnumerator()
        {
            return Tokenize().GetEnumerator();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return Tokenize().GetEnumerator();
        }
    }

    [Serializable]
    internal class CountNotTokenizeCharException : Exception
    {
        public CountNotTokenizeCharException(string code, int cursor) : base($"parse error: {code} could not be parsed on col {cursor} ({code.Substring(cursor)})")
        {
        }
    }
}