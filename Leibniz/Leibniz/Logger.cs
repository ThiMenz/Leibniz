using System;
using System.IO;
using System.Text;

namespace CUSTOM_LOGGING
{
    public static class Logger
    {
        // Path to your log file (you can make this configurable)
        private static readonly string LogFilePath = Path.Combine(
            AppDomain.CurrentDomain.BaseDirectory, "application.log");

        // The writer instance (nullable so we can reset it)
        private static StreamWriter? _writer;
        private static readonly object _writerLock = new();

        /// <summary>
        /// Lazily creates (or returns) the StreamWriter for appending to the log.
        /// </summary>
        private static StreamWriter GetWriter()
        {
            if (_writer == null)
            {
                lock (_writerLock)
                {
                    if (_writer == null)
                    {
                        _writer = new StreamWriter(new FileStream(
                            LogFilePath,
                            FileMode.Append,
                            FileAccess.Write,
                            FileShare.Read))
                        {
                            AutoFlush = true
                        };
                    }
                }
            }
            return _writer;
        }

        /// <summary>
        /// Writes an empty line to both console and log.
        /// </summary>
        public static void Log()
        {
            Console.WriteLine();
            GetWriter().WriteLine();
        }

        /// <summary>
        /// Writes the given message both to the console and to the log file.
        /// </summary>
        public static void Log(object message)
        {
            Console.WriteLine(message);
            GetWriter().WriteLine($"{DateTime.Now:yyyy-MM-dd HH:mm:ss.fff} | {message}");
        }

        /// <summary>
        /// Closes any open writer, deletes the log file if it exists,
        /// so that subsequent Log calls start a fresh file.
        /// </summary>
        public static void ClearLog()
        {
            lock (_writerLock)
            {
                // 1) Close & dispose the writer if it's open
                if (_writer != null)
                {
                    _writer.Close();
                    _writer.Dispose();
                    _writer = null;
                }

                // 2) Delete the file on disk if it exists
                if (File.Exists(LogFilePath))
                {
                    File.Delete(LogFilePath);
                }
            }
        }
    }
}
