--
-- PostgreSQL database dump
--

-- Dumped from database version 14.1 (Ubuntu 14.1-2.pgdg20.04+1)
-- Dumped by pg_dump version 14.1 (Ubuntu 14.1-2.pgdg20.04+1)

SET statement_timeout = 0;
SET lock_timeout = 0;
SET idle_in_transaction_session_timeout = 0;
SET client_encoding = 'UTF8';
SET standard_conforming_strings = on;
SELECT pg_catalog.set_config('search_path', '', false);
SET check_function_bodies = false;
SET xmloption = content;
SET client_min_messages = warning;
SET row_security = off;

SET default_tablespace = '';

SET default_table_access_method = heap;

--
-- Name: r1_2; Type: TABLE; Schema: public; Owner: postgres
--

CREATE TABLE public.r1_2 (
    n1 public.int4_faure,
    n2 public.int4_faure,
    condition text[]
);


ALTER TABLE public.r1_2 OWNER TO postgres;

--
-- Data for Name: r1_2; Type: TABLE DATA; Schema: public; Owner: postgres
--

COPY public.r1_2 (n1, n2, condition) FROM stdin;
1	1	{"Or(And(x1 == 1))"}
x1	1	{"Or(And(x1 == 1, x2 == 1))"}
x2	1	{"Or(And(x2 == 1, x3 == 1), And(x2 == 1))"}
x3	1	{"Or(And(x3 == 1, x4 == 1), And(x3 == 1))"}
x4	1	{"Or(And(x4 == 1, x5 == 1), And(x4 == 1))"}
x5	1	{"Or(And(x5 == 1, x6 == 1), And(x5 == 1))"}
x6	1	{"Or(And(x6 == 1, x7 == 1), And(x6 == 1))"}
x7	1	{"Or(And(x7 == 1, x8 == 1), And(x7 == 1))"}
x8	1	{"Or(And(x8 == 1, x9 == 1), And(x8 == 1))"}
x9	1	{"Or(And(x9 == 1, x10 == 1), And(x9 == 1))"}
x10	1	{"Or(And(x10 == 1))"}
1	x1	{"Or(And(1 == x1), And(x1 == 1, 1 == x1))"}
1	x2	{"Or(And(x1 == x1, x1 == x2), And(x1 == x2, x2 == x2), And(1 == x1, x1 == x2), And(1 == x2, x2 == x2))"}
1	x3	{"Or(And(x1 == x2, x2 == x3), And(x1 == x3, x3 == x3), And(1 == x2, x2 == x3), And(1 == x3, x3 == x3))"}
1	x4	{"Or(And(x1 == x3, x3 == x4), And(x1 == x4, x4 == x4), And(1 == x3, x3 == x4), And(1 == x4, x4 == x4))"}
1	x5	{"Or(And(x1 == x4, x4 == x5), And(x1 == x5, x5 == x5), And(1 == x4, x4 == x5), And(1 == x5, x5 == x5))"}
1	x6	{"Or(And(x1 == x5, x5 == x6), And(x1 == x6, x6 == x6), And(1 == x5, x5 == x6), And(1 == x6, x6 == x6))"}
1	x7	{"Or(And(x1 == x6, x6 == x7), And(x1 == x7, x7 == x7), And(1 == x6, x6 == x7), And(1 == x7, x7 == x7))"}
1	x8	{"Or(And(x1 == x7, x7 == x8), And(x1 == x8, x8 == x8), And(1 == x7, x7 == x8), And(1 == x8, x8 == x8))"}
1	x9	{"Or(And(x1 == x8, x8 == x9), And(x1 == x9, x9 == x9), And(1 == x8, x8 == x9), And(1 == x9, x9 == x9))"}
1	x10	{"Or(And(x1 == x9, x9 == x10), And(x1 == x10, x10 == x10), And(1 == x9, x9 == x10), And(1 == x10, x10 == x10))"}
1	2	{"Or(And(x1 == x10, x10 == 2), And(1 == x10, x10 == 2))"}
x1	x1	{"Or(And(x1 == 1, x2 == 1, 1 == x1))"}
x1	x2	{"Or(And(x1 == 1, x2 == x1, x1 == x2), And(x1 == 1, x2 == x2))"}
x1	x3	{"Or(And(x1 == 1, x2 == x2, x2 == x3), And(x1 == 1, x2 == x3, x3 == x3))"}
x1	x4	{"Or(And(x1 == 1, x2 == x3, x3 == x4), And(x1 == 1, x2 == x4, x4 == x4))"}
x1	x5	{"Or(And(x1 == 1, x2 == x4, x4 == x5), And(x1 == 1, x2 == x5, x5 == x5))"}
x1	x6	{"Or(And(x1 == 1, x2 == x5, x5 == x6), And(x1 == 1, x2 == x6, x6 == x6))"}
x1	x7	{"Or(And(x1 == 1, x2 == x6, x6 == x7), And(x1 == 1, x2 == x7, x7 == x7))"}
x1	x8	{"Or(And(x1 == 1, x2 == x7, x7 == x8), And(x1 == 1, x2 == x8, x8 == x8))"}
x1	x9	{"Or(And(x1 == 1, x2 == x8, x8 == x9), And(x1 == 1, x2 == x9, x9 == x9))"}
x1	x10	{"Or(And(x1 == 1, x2 == x9, x9 == x10), And(x1 == 1, x2 == x10, x10 == x10))"}
x1	2	{"Or(And(x1 == 1, x2 == x10, x10 == 2))"}
x2	x1	{"Or(And(x2 == 1, x3 == 1, 1 == x1), And(x2 == 1, 1 == x1))"}
x2	x2	{"Or(And(x2 == 1, x3 == x1, x1 == x2), And(x2 == 1, x3 == x2, x2 == x2), And(x2 == 1, x2 == x1, x1 == x2), And(x2 == 1, x2 == x2))"}
x2	x3	{"Or(And(x2 == 1, x3 == x2, x2 == x3), And(x2 == 1, x3 == x3), And(x2 == 1, x2 == x2, x2 == x3), And(x2 == 1, x2 == x3, x3 == x3))"}
x2	x4	{"Or(And(x2 == 1, x3 == x3, x3 == x4), And(x2 == 1, x3 == x4, x4 == x4), And(x2 == 1, x2 == x3, x3 == x4), And(x2 == 1, x2 == x4, x4 == x4))"}
x2	x5	{"Or(And(x2 == 1, x3 == x4, x4 == x5), And(x2 == 1, x3 == x5, x5 == x5), And(x2 == 1, x2 == x4, x4 == x5), And(x2 == 1, x2 == x5, x5 == x5))"}
x2	x6	{"Or(And(x2 == 1, x3 == x5, x5 == x6), And(x2 == 1, x3 == x6, x6 == x6), And(x2 == 1, x2 == x5, x5 == x6), And(x2 == 1, x2 == x6, x6 == x6))"}
x2	x7	{"Or(And(x2 == 1, x3 == x6, x6 == x7), And(x2 == 1, x3 == x7, x7 == x7), And(x2 == 1, x2 == x6, x6 == x7), And(x2 == 1, x2 == x7, x7 == x7))"}
x2	x8	{"Or(And(x2 == 1, x3 == x7, x7 == x8), And(x2 == 1, x3 == x8, x8 == x8), And(x2 == 1, x2 == x7, x7 == x8), And(x2 == 1, x2 == x8, x8 == x8))"}
x2	x9	{"Or(And(x2 == 1, x3 == x8, x8 == x9), And(x2 == 1, x3 == x9, x9 == x9), And(x2 == 1, x2 == x8, x8 == x9), And(x2 == 1, x2 == x9, x9 == x9))"}
x2	x10	{"Or(And(x2 == 1, x3 == x9, x9 == x10), And(x2 == 1, x3 == x10, x10 == x10), And(x2 == 1, x2 == x9, x9 == x10), And(x2 == 1, x2 == x10, x10 == x10))"}
x2	2	{"Or(And(x2 == 1, x3 == x10, x10 == 2), And(x2 == 1, x2 == x10, x10 == 2))"}
x3	x1	{"Or(And(x3 == 1, x4 == 1, 1 == x1), And(x3 == 1, 1 == x1))"}
x3	x2	{"Or(And(x3 == 1, x4 == x1, x1 == x2), And(x3 == 1, x4 == x2, x2 == x2), And(x3 == 1, x3 == x1, x1 == x2), And(x3 == 1, x3 == x2, x2 == x2))"}
x3	x3	{"Or(And(x3 == 1, x4 == x2, x2 == x3), And(x3 == 1, x4 == x3, x3 == x3), And(x3 == 1, x3 == x2, x2 == x3), And(x3 == 1, x3 == x3))"}
x3	x4	{"Or(And(x3 == 1, x4 == x3, x3 == x4), And(x3 == 1, x4 == x4), And(x3 == 1, x3 == x3, x3 == x4), And(x3 == 1, x3 == x4, x4 == x4))"}
x3	x5	{"Or(And(x3 == 1, x4 == x4, x4 == x5), And(x3 == 1, x4 == x5, x5 == x5), And(x3 == 1, x3 == x4, x4 == x5), And(x3 == 1, x3 == x5, x5 == x5))"}
x3	x6	{"Or(And(x3 == 1, x4 == x5, x5 == x6), And(x3 == 1, x4 == x6, x6 == x6), And(x3 == 1, x3 == x5, x5 == x6), And(x3 == 1, x3 == x6, x6 == x6))"}
x3	x7	{"Or(And(x3 == 1, x4 == x6, x6 == x7), And(x3 == 1, x4 == x7, x7 == x7), And(x3 == 1, x3 == x6, x6 == x7), And(x3 == 1, x3 == x7, x7 == x7))"}
x3	x8	{"Or(And(x3 == 1, x4 == x7, x7 == x8), And(x3 == 1, x4 == x8, x8 == x8), And(x3 == 1, x3 == x7, x7 == x8), And(x3 == 1, x3 == x8, x8 == x8))"}
x3	x9	{"Or(And(x3 == 1, x4 == x8, x8 == x9), And(x3 == 1, x4 == x9, x9 == x9), And(x3 == 1, x3 == x8, x8 == x9), And(x3 == 1, x3 == x9, x9 == x9))"}
x3	x10	{"Or(And(x3 == 1, x4 == x9, x9 == x10), And(x3 == 1, x4 == x10, x10 == x10), And(x3 == 1, x3 == x9, x9 == x10), And(x3 == 1, x3 == x10, x10 == x10))"}
x3	2	{"Or(And(x3 == 1, x4 == x10, x10 == 2), And(x3 == 1, x3 == x10, x10 == 2))"}
x4	x1	{"Or(And(x4 == 1, x5 == 1, 1 == x1), And(x4 == 1, 1 == x1))"}
x4	x2	{"Or(And(x4 == 1, x5 == x1, x1 == x2), And(x4 == 1, x5 == x2, x2 == x2), And(x4 == 1, x4 == x1, x1 == x2), And(x4 == 1, x4 == x2, x2 == x2))"}
x4	x3	{"Or(And(x4 == 1, x5 == x2, x2 == x3), And(x4 == 1, x5 == x3, x3 == x3), And(x4 == 1, x4 == x2, x2 == x3), And(x4 == 1, x4 == x3, x3 == x3))"}
x4	x4	{"Or(And(x4 == 1, x5 == x3, x3 == x4), And(x4 == 1, x5 == x4, x4 == x4), And(x4 == 1, x4 == x3, x3 == x4), And(x4 == 1, x4 == x4))"}
x4	x5	{"Or(And(x4 == 1, x5 == x4, x4 == x5), And(x4 == 1, x5 == x5), And(x4 == 1, x4 == x4, x4 == x5), And(x4 == 1, x4 == x5, x5 == x5))"}
x4	x6	{"Or(And(x4 == 1, x5 == x5, x5 == x6), And(x4 == 1, x5 == x6, x6 == x6), And(x4 == 1, x4 == x5, x5 == x6), And(x4 == 1, x4 == x6, x6 == x6))"}
x4	x7	{"Or(And(x4 == 1, x5 == x6, x6 == x7), And(x4 == 1, x5 == x7, x7 == x7), And(x4 == 1, x4 == x6, x6 == x7), And(x4 == 1, x4 == x7, x7 == x7))"}
x4	x8	{"Or(And(x4 == 1, x5 == x7, x7 == x8), And(x4 == 1, x5 == x8, x8 == x8), And(x4 == 1, x4 == x7, x7 == x8), And(x4 == 1, x4 == x8, x8 == x8))"}
x4	x9	{"Or(And(x4 == 1, x5 == x8, x8 == x9), And(x4 == 1, x5 == x9, x9 == x9), And(x4 == 1, x4 == x8, x8 == x9), And(x4 == 1, x4 == x9, x9 == x9))"}
x4	x10	{"Or(And(x4 == 1, x5 == x9, x9 == x10), And(x4 == 1, x5 == x10, x10 == x10), And(x4 == 1, x4 == x9, x9 == x10), And(x4 == 1, x4 == x10, x10 == x10))"}
x4	2	{"Or(And(x4 == 1, x5 == x10, x10 == 2), And(x4 == 1, x4 == x10, x10 == 2))"}
x5	x1	{"Or(And(x5 == 1, x6 == 1, 1 == x1), And(x5 == 1, 1 == x1))"}
x5	x2	{"Or(And(x5 == 1, x6 == x1, x1 == x2), And(x5 == 1, x6 == x2, x2 == x2), And(x5 == 1, x5 == x1, x1 == x2), And(x5 == 1, x5 == x2, x2 == x2))"}
x5	x3	{"Or(And(x5 == 1, x6 == x2, x2 == x3), And(x5 == 1, x6 == x3, x3 == x3), And(x5 == 1, x5 == x2, x2 == x3), And(x5 == 1, x5 == x3, x3 == x3))"}
x5	x4	{"Or(And(x5 == 1, x6 == x3, x3 == x4), And(x5 == 1, x6 == x4, x4 == x4), And(x5 == 1, x5 == x3, x3 == x4), And(x5 == 1, x5 == x4, x4 == x4))"}
x5	x5	{"Or(And(x5 == 1, x6 == x4, x4 == x5), And(x5 == 1, x6 == x5, x5 == x5), And(x5 == 1, x5 == x4, x4 == x5), And(x5 == 1, x5 == x5))"}
x5	x6	{"Or(And(x5 == 1, x6 == x5, x5 == x6), And(x5 == 1, x6 == x6), And(x5 == 1, x5 == x5, x5 == x6), And(x5 == 1, x5 == x6, x6 == x6))"}
x5	x7	{"Or(And(x5 == 1, x6 == x6, x6 == x7), And(x5 == 1, x6 == x7, x7 == x7), And(x5 == 1, x5 == x6, x6 == x7), And(x5 == 1, x5 == x7, x7 == x7))"}
x5	x8	{"Or(And(x5 == 1, x6 == x7, x7 == x8), And(x5 == 1, x6 == x8, x8 == x8), And(x5 == 1, x5 == x7, x7 == x8), And(x5 == 1, x5 == x8, x8 == x8))"}
x5	x9	{"Or(And(x5 == 1, x6 == x8, x8 == x9), And(x5 == 1, x6 == x9, x9 == x9), And(x5 == 1, x5 == x8, x8 == x9), And(x5 == 1, x5 == x9, x9 == x9))"}
x5	x10	{"Or(And(x5 == 1, x6 == x9, x9 == x10), And(x5 == 1, x6 == x10, x10 == x10), And(x5 == 1, x5 == x9, x9 == x10), And(x5 == 1, x5 == x10, x10 == x10))"}
x5	2	{"Or(And(x5 == 1, x6 == x10, x10 == 2), And(x5 == 1, x5 == x10, x10 == 2))"}
x6	x1	{"Or(And(x6 == 1, x7 == 1, 1 == x1), And(x6 == 1, 1 == x1))"}
x6	x2	{"Or(And(x6 == 1, x7 == x1, x1 == x2), And(x6 == 1, x7 == x2, x2 == x2), And(x6 == 1, x6 == x1, x1 == x2), And(x6 == 1, x6 == x2, x2 == x2))"}
x6	x3	{"Or(And(x6 == 1, x7 == x2, x2 == x3), And(x6 == 1, x7 == x3, x3 == x3), And(x6 == 1, x6 == x2, x2 == x3), And(x6 == 1, x6 == x3, x3 == x3))"}
x6	x4	{"Or(And(x6 == 1, x7 == x3, x3 == x4), And(x6 == 1, x7 == x4, x4 == x4), And(x6 == 1, x6 == x3, x3 == x4), And(x6 == 1, x6 == x4, x4 == x4))"}
x6	x5	{"Or(And(x6 == 1, x7 == x4, x4 == x5), And(x6 == 1, x7 == x5, x5 == x5), And(x6 == 1, x6 == x4, x4 == x5), And(x6 == 1, x6 == x5, x5 == x5))"}
x6	x6	{"Or(And(x6 == 1, x7 == x5, x5 == x6), And(x6 == 1, x7 == x6, x6 == x6), And(x6 == 1, x6 == x5, x5 == x6), And(x6 == 1, x6 == x6))"}
x6	x7	{"Or(And(x6 == 1, x7 == x6, x6 == x7), And(x6 == 1, x7 == x7), And(x6 == 1, x6 == x6, x6 == x7), And(x6 == 1, x6 == x7, x7 == x7))"}
x6	x8	{"Or(And(x6 == 1, x7 == x7, x7 == x8), And(x6 == 1, x7 == x8, x8 == x8), And(x6 == 1, x6 == x7, x7 == x8), And(x6 == 1, x6 == x8, x8 == x8))"}
x6	x9	{"Or(And(x6 == 1, x7 == x8, x8 == x9), And(x6 == 1, x7 == x9, x9 == x9), And(x6 == 1, x6 == x8, x8 == x9), And(x6 == 1, x6 == x9, x9 == x9))"}
x6	x10	{"Or(And(x6 == 1, x7 == x9, x9 == x10), And(x6 == 1, x7 == x10, x10 == x10), And(x6 == 1, x6 == x9, x9 == x10), And(x6 == 1, x6 == x10, x10 == x10))"}
x6	2	{"Or(And(x6 == 1, x7 == x10, x10 == 2), And(x6 == 1, x6 == x10, x10 == 2))"}
x7	x1	{"Or(And(x7 == 1, x8 == 1, 1 == x1), And(x7 == 1, 1 == x1))"}
x7	x2	{"Or(And(x7 == 1, x8 == x1, x1 == x2), And(x7 == 1, x8 == x2, x2 == x2), And(x7 == 1, x7 == x1, x1 == x2), And(x7 == 1, x7 == x2, x2 == x2))"}
x7	x3	{"Or(And(x7 == 1, x8 == x2, x2 == x3), And(x7 == 1, x8 == x3, x3 == x3), And(x7 == 1, x7 == x2, x2 == x3), And(x7 == 1, x7 == x3, x3 == x3))"}
x7	x4	{"Or(And(x7 == 1, x8 == x3, x3 == x4), And(x7 == 1, x8 == x4, x4 == x4), And(x7 == 1, x7 == x3, x3 == x4), And(x7 == 1, x7 == x4, x4 == x4))"}
x7	x5	{"Or(And(x7 == 1, x8 == x4, x4 == x5), And(x7 == 1, x8 == x5, x5 == x5), And(x7 == 1, x7 == x4, x4 == x5), And(x7 == 1, x7 == x5, x5 == x5))"}
x7	x6	{"Or(And(x7 == 1, x8 == x5, x5 == x6), And(x7 == 1, x8 == x6, x6 == x6), And(x7 == 1, x7 == x5, x5 == x6), And(x7 == 1, x7 == x6, x6 == x6))"}
x7	x7	{"Or(And(x7 == 1, x8 == x6, x6 == x7), And(x7 == 1, x8 == x7, x7 == x7), And(x7 == 1, x7 == x6, x6 == x7), And(x7 == 1, x7 == x7))"}
x7	x8	{"Or(And(x7 == 1, x8 == x7, x7 == x8), And(x7 == 1, x8 == x8), And(x7 == 1, x7 == x7, x7 == x8), And(x7 == 1, x7 == x8, x8 == x8))"}
x7	x9	{"Or(And(x7 == 1, x8 == x8, x8 == x9), And(x7 == 1, x8 == x9, x9 == x9), And(x7 == 1, x7 == x8, x8 == x9), And(x7 == 1, x7 == x9, x9 == x9))"}
x7	x10	{"Or(And(x7 == 1, x8 == x9, x9 == x10), And(x7 == 1, x8 == x10, x10 == x10), And(x7 == 1, x7 == x9, x9 == x10), And(x7 == 1, x7 == x10, x10 == x10))"}
x7	2	{"Or(And(x7 == 1, x8 == x10, x10 == 2), And(x7 == 1, x7 == x10, x10 == 2))"}
x8	x1	{"Or(And(x8 == 1, x9 == 1, 1 == x1), And(x8 == 1, 1 == x1))"}
x8	x2	{"Or(And(x8 == 1, x9 == x1, x1 == x2), And(x8 == 1, x9 == x2, x2 == x2), And(x8 == 1, x8 == x1, x1 == x2), And(x8 == 1, x8 == x2, x2 == x2))"}
x8	x3	{"Or(And(x8 == 1, x9 == x2, x2 == x3), And(x8 == 1, x9 == x3, x3 == x3), And(x8 == 1, x8 == x2, x2 == x3), And(x8 == 1, x8 == x3, x3 == x3))"}
x8	x4	{"Or(And(x8 == 1, x9 == x3, x3 == x4), And(x8 == 1, x9 == x4, x4 == x4), And(x8 == 1, x8 == x3, x3 == x4), And(x8 == 1, x8 == x4, x4 == x4))"}
x8	x5	{"Or(And(x8 == 1, x9 == x4, x4 == x5), And(x8 == 1, x9 == x5, x5 == x5), And(x8 == 1, x8 == x4, x4 == x5), And(x8 == 1, x8 == x5, x5 == x5))"}
x8	x6	{"Or(And(x8 == 1, x9 == x5, x5 == x6), And(x8 == 1, x9 == x6, x6 == x6), And(x8 == 1, x8 == x5, x5 == x6), And(x8 == 1, x8 == x6, x6 == x6))"}
x8	x7	{"Or(And(x8 == 1, x9 == x6, x6 == x7), And(x8 == 1, x9 == x7, x7 == x7), And(x8 == 1, x8 == x6, x6 == x7), And(x8 == 1, x8 == x7, x7 == x7))"}
x8	x8	{"Or(And(x8 == 1, x9 == x7, x7 == x8), And(x8 == 1, x9 == x8, x8 == x8), And(x8 == 1, x8 == x7, x7 == x8), And(x8 == 1, x8 == x8))"}
x8	x9	{"Or(And(x8 == 1, x9 == x8, x8 == x9), And(x8 == 1, x9 == x9), And(x8 == 1, x8 == x8, x8 == x9), And(x8 == 1, x8 == x9, x9 == x9))"}
x8	x10	{"Or(And(x8 == 1, x9 == x9, x9 == x10), And(x8 == 1, x9 == x10, x10 == x10), And(x8 == 1, x8 == x9, x9 == x10), And(x8 == 1, x8 == x10, x10 == x10))"}
x8	2	{"Or(And(x8 == 1, x9 == x10, x10 == 2), And(x8 == 1, x8 == x10, x10 == 2))"}
x9	x1	{"Or(And(x9 == 1, x10 == 1, 1 == x1), And(x9 == 1, 1 == x1))"}
x9	x2	{"Or(And(x9 == 1, x10 == x1, x1 == x2), And(x9 == 1, x10 == x2, x2 == x2), And(x9 == 1, x9 == x1, x1 == x2), And(x9 == 1, x9 == x2, x2 == x2))"}
x9	x3	{"Or(And(x9 == 1, x10 == x2, x2 == x3), And(x9 == 1, x10 == x3, x3 == x3), And(x9 == 1, x9 == x2, x2 == x3), And(x9 == 1, x9 == x3, x3 == x3))"}
x9	x4	{"Or(And(x9 == 1, x10 == x3, x3 == x4), And(x9 == 1, x10 == x4, x4 == x4), And(x9 == 1, x9 == x3, x3 == x4), And(x9 == 1, x9 == x4, x4 == x4))"}
x9	x5	{"Or(And(x9 == 1, x10 == x4, x4 == x5), And(x9 == 1, x10 == x5, x5 == x5), And(x9 == 1, x9 == x4, x4 == x5), And(x9 == 1, x9 == x5, x5 == x5))"}
x9	x6	{"Or(And(x9 == 1, x10 == x5, x5 == x6), And(x9 == 1, x10 == x6, x6 == x6), And(x9 == 1, x9 == x5, x5 == x6), And(x9 == 1, x9 == x6, x6 == x6))"}
x9	x7	{"Or(And(x9 == 1, x10 == x6, x6 == x7), And(x9 == 1, x10 == x7, x7 == x7), And(x9 == 1, x9 == x6, x6 == x7), And(x9 == 1, x9 == x7, x7 == x7))"}
x9	x8	{"Or(And(x9 == 1, x10 == x7, x7 == x8), And(x9 == 1, x10 == x8, x8 == x8), And(x9 == 1, x9 == x7, x7 == x8), And(x9 == 1, x9 == x8, x8 == x8))"}
x9	x9	{"Or(And(x9 == 1, x10 == x8, x8 == x9), And(x9 == 1, x10 == x9, x9 == x9), And(x9 == 1, x9 == x8, x8 == x9), And(x9 == 1, x9 == x9))"}
x9	x10	{"Or(And(x9 == 1, x10 == x9, x9 == x10), And(x9 == 1, x10 == x10), And(x9 == 1, x9 == x9, x9 == x10), And(x9 == 1, x9 == x10, x10 == x10))"}
x9	2	{"Or(And(x9 == 1, x10 == x10, x10 == 2), And(x9 == 1, x9 == x10, x10 == 2))"}
x10	x2	{"Or(And(x10 == 1, 2 == x1, x1 == x2), And(x10 == 1, 2 == x2, x2 == x2), And(x10 == 1, x10 == x1, x1 == x2), And(x10 == 1, x10 == x2, x2 == x2))"}
x10	x3	{"Or(And(x10 == 1, 2 == x2, x2 == x3), And(x10 == 1, 2 == x3, x3 == x3), And(x10 == 1, x10 == x2, x2 == x3), And(x10 == 1, x10 == x3, x3 == x3))"}
x10	x4	{"Or(And(x10 == 1, 2 == x3, x3 == x4), And(x10 == 1, 2 == x4, x4 == x4), And(x10 == 1, x10 == x3, x3 == x4), And(x10 == 1, x10 == x4, x4 == x4))"}
x10	x5	{"Or(And(x10 == 1, 2 == x4, x4 == x5), And(x10 == 1, 2 == x5, x5 == x5), And(x10 == 1, x10 == x4, x4 == x5), And(x10 == 1, x10 == x5, x5 == x5))"}
x10	x6	{"Or(And(x10 == 1, 2 == x5, x5 == x6), And(x10 == 1, 2 == x6, x6 == x6), And(x10 == 1, x10 == x5, x5 == x6), And(x10 == 1, x10 == x6, x6 == x6))"}
x10	x7	{"Or(And(x10 == 1, 2 == x6, x6 == x7), And(x10 == 1, 2 == x7, x7 == x7), And(x10 == 1, x10 == x6, x6 == x7), And(x10 == 1, x10 == x7, x7 == x7))"}
x10	x8	{"Or(And(x10 == 1, 2 == x7, x7 == x8), And(x10 == 1, 2 == x8, x8 == x8), And(x10 == 1, x10 == x7, x7 == x8), And(x10 == 1, x10 == x8, x8 == x8))"}
x10	x9	{"Or(And(x10 == 1, 2 == x8, x8 == x9), And(x10 == 1, 2 == x9, x9 == x9), And(x10 == 1, x10 == x8, x8 == x9), And(x10 == 1, x10 == x9, x9 == x9))"}
x10	x10	{"Or(And(x10 == 1, 2 == x9, x9 == x10), And(x10 == 1, 2 == x10, x10 == x10), And(x10 == 1, x10 == x9, x9 == x10), And(x10 == 1, x10 == x10))"}
x10	2	{"Or(And(x10 == 1, 2 == x10, x10 == 2), And(x10 == 1, x10 == x10, x10 == 2))"}
x10	x1	{"Or(And(x10 == 1, 1 == x1))"}
\.


--
-- PostgreSQL database dump complete
--

