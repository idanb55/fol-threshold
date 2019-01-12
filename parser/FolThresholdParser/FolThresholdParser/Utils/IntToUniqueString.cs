using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace FolThresholdParser.Utils
{
    public class StringUtils
    {
        public static string IntToUniqueString(int value)
        {
            return IntToUniqueString(value,
                new[]
                {
                    'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T',
                    'U', 'V', 'W', 'X', 'Y', 'Z'
                });
        }

        private static string IntToUniqueString(int value, char[] baseChars)
        {
            string result = string.Empty;
            int targetBase = baseChars.Length;

            do
            {
                result = baseChars[value % targetBase] + result;
                value = value / targetBase;
            }
            while (value > 0);

            return result;
        }
    }
}
