/*
** Copyright (C) 2009-2016  Michael Roland <mi.roland@gmail.com>
**
** This program is free software: you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation, either version 3 of the License, or
** (at your option) any later version.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program.  If not, see <http://www.gnu.org/licenses/>.
**
*/
package at.mroland.utils;

import java.nio.charset.Charset;

/**
 * Utilities for conversions between byte-arrays and strings.
 */
public final class StringUtils {
    public static String bytesToHex(byte[] b) {
        if (b != null) {
            StringBuilder s = new StringBuilder(2 * b.length);

            for (int i = 0; i < b.length; ++i) {
                final String t = Integer.toHexString(b[i]);
                final int l = t.length();
                if (l > 2) {
                    s.append(t.substring(l - 2));
                } else {
                    if (l == 1) {
                        s.append("0");
                    }
                    s.append(t);
                }
            }

            return s.toString();
        } else {
            return "";
        }
    }

    public static String bytesToReverseHex(byte[] b) {
        if (b != null) {
            StringBuilder s = new StringBuilder(2 * b.length);

            for (int i = (b.length - 1); i >= 0; --i) {
                final String t = Integer.toHexString(b[i]);
                final int l = t.length();
                if (l > 2) {
                    s.append(t.substring(l - 2));
                } else {
                    if (l == 1) {
                        s.append("0");
                    }
                    s.append(t);
                }
            }

            return s.toString();
        } else {
            return "";
        }
    }

    public static String bytesToAscii(byte[] b) {
        String s = "";

        try {
            s = new String(b, Charset.forName("US-ASCII"));
        } catch (Exception e) {}

        return s;
    }

    public static String bytesToAscii(byte[] b, int offset, int length) {
        String s = "";

        try {
            s = new String(b, offset, length, Charset.forName("US-ASCII"));
        } catch (Exception e) {}

        return s;
    }

    public static byte[] asciiToBytes(String s) {
        byte[] b = new byte[0];

        try {
            b = s.getBytes(Charset.forName("US-ASCII"));
        } catch (Exception e) {}

        return b;
    }

    public static String bytesToUtf8(byte[] b) {
        String s = "";

        try {
            s = new String(b, Charset.forName("UTF-8"));
        } catch (Exception e) {}

        return s;
    }

    public static String bytesToUtf8(byte[] b, int offset, int length) {
        String s = "";

        try {
            s = new String(b, offset, length, Charset.forName("UTF-8"));
        } catch (Exception e) {}

        return s;
    }

    public static byte[] utf8ToBytes(String s) {
        byte[] b = new byte[0];

        try {
            b = s.getBytes(Charset.forName("UTF-8"));
        } catch (Exception e) {}

        return b;
    }

    public static String bytesToUtf16(byte[] b) {
        String s = "";

        try {
            s = new String(b, Charset.forName("UTF-16"));
        } catch (Exception e) {}

        return s;
    }

    public static String bytesToUtf16(byte[] b, int offset, int length) {
        String s = "";

        try {
            s = new String(b, offset, length, Charset.forName("UTF-16"));
        } catch (Exception e) {}

        return s;
    }

    public static byte[] utf16ToBytes(String s) {
        byte[] b = new byte[0];

        try {
            b = s.getBytes(Charset.forName("UTF-16"));
        } catch (Exception e) {}

        return b;
    }

    public static byte[] hexToBytes(String s) {
        s = s.replace(" ", "").replace(":", "").replace("-", "").replace("0x", "");

        final int len = s.length();
        final int rem = len % 2;

        byte[] ret = new byte[len / 2 + rem];

        if (rem != 0) {
            try {
                ret[0] = (byte)(Integer.parseInt(s.substring(0, 1), 16) & 0x00F);
            } catch (Exception e) {
                ret[0] = 0;
            }
        }

        for (int i = rem; i < len; i += 2) {
            try {
                ret[i / 2 + rem] = (byte)(Integer.parseInt(s.substring(i, i + 2), 16) & 0x0FF);
            } catch (Exception e) {
                ret[i / 2 + rem] = 0;
            }
        }

        return ret;
    }

    public static String repeat(String s, int count) {
        StringBuilder builder = new StringBuilder(s.length() * count);

        for (int i = 0; i < count; ++i) {
            builder.append(s);
        }

        return builder.toString();
    }

    private StringUtils() {}
}
